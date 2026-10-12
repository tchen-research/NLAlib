import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Removing an uncoupled scalar coordinate from a characteristic polynomial

A coordinate with zero cross row and column contributes exactly one scalar
factor. The remaining coordinates may be indexed by any chosen equivalence.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace NLAlib

/-- Isolate a chosen finite coordinate as the first singleton summand,
with every remaining coordinate in its original increasing order.
Supports the repeated-root restoration in converse interlacing. -/
def finOneSumSuccAboveEquiv {n : ℕ} (p : Fin (n + 1)) :
    Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  Equiv.ofBijective (Sum.elim (fun _ => p) p.succAbove) (by
    constructor
    · intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (Subsingleton.elim i j)
        | inr j => exact ((Fin.ne_succAbove p j) h).elim
      | inr i =>
        cases y with
        | inl j => exact ((Fin.succAbove_ne p i) h).elim
        | inr j => exact congrArg Sum.inr (Fin.succAbove_right_injective h)
    · intro i
      exact Fin.succAboveCases p ⟨Sum.inl 0, rfl⟩ (fun j => ⟨Sum.inr j, rfl⟩) i)

/-- The singled-out coordinate of `finOneSumSuccAboveEquiv` is the chosen
index. Supports repeated-root restoration in converse interlacing. -/
@[simp] theorem finOneSumSuccAboveEquiv_inl {n : ℕ} (p : Fin (n + 1)) (i : Fin 1) :
    finOneSumSuccAboveEquiv p (Sum.inl i) = p := rfl

/-- The remaining coordinates of `finOneSumSuccAboveEquiv` are exactly
`Fin.succAbove`. Supports repeated-root restoration in converse interlacing. -/
@[simp] theorem finOneSumSuccAboveEquiv_inr {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    finOneSumSuccAboveEquiv p (Sum.inr i) = p.succAbove i := rfl

/-- An uncoupled scalar coordinate contributes one linear characteristic
factor, with the other coordinates in any specified order. Horn–Johnson
2013, Section 1.2; converse-interlacing restoration helper. -/
theorem charpoly_eq_mul_of_isolated_equiv {m n K : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing K]
    (A : Matrix m m K) (e : Fin 1 ⊕ n ≃ m)
    (h : ∀ j, A (e (Sum.inl 0)) (e (Sum.inr j)) = 0 ∧
      A (e (Sum.inr j)) (e (Sum.inl 0)) = 0) :
    A.charpoly = (X - C (A (e (Sum.inl 0)) (e (Sum.inl 0)))) *
      (A.submatrix (fun j => e (Sum.inr j)) (fun j => e (Sum.inr j))).charpoly := by
  let B := A.submatrix (fun j => e (Sum.inr j)) (fun j => e (Sum.inr j))
  have hblocks : A.submatrix e e = Matrix.fromBlocks
      (Matrix.diagonal (fun _ : Fin 1 => A (e (Sum.inl 0)) (e (Sum.inl 0)))) 0 0 B := by
    ext i j
    cases i with
    | inl i =>
      fin_cases i
      cases j with
      | inl j => fin_cases j; simp
      | inr j => exact (h j).1
    | inr i =>
      cases j with
      | inl j => fin_cases j; exact (h i).2
      | inr j => rfl
  rw [← Matrix.charpoly_reindex e.symm A]
  change (A.submatrix e e).charpoly = _
  rw [hblocks, Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_diagonal]
  simp [B]

end NLAlib

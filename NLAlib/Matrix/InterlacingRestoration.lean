import NLAlib.ForMathlib.LinearAlgebra.IsolatedCharpoly
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Data.Real.Basic

/-!
# Restoring an uncoupled repeated eigenvalue

Inserting a zero coupling at any original diagonal coordinate restores its
linear characteristic factor in both rank-one and bordered constructions.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Inserting a zero coupling in a diagonal rank-one update restores an
uncoupled scalar characteristic factor. Horn–Johnson 2013, Theorem 4.3.26;
repeated-root converse-interlacing restoration helper. -/
theorem charpoly_diagonal_add_vecMulVec_insertNth {n : ℕ}
    (d : Fin (n + 1) → ℝ) (p : Fin (n + 1)) (v : Fin n → ℝ) :
    (Matrix.diagonal d + Matrix.vecMulVec (p.insertNth 0 v) (p.insertNth 0 v)).charpoly =
      (X - C (d p)) *
        (Matrix.diagonal (d ∘ p.succAbove) + Matrix.vecMulVec v v).charpoly := by
  let A := Matrix.diagonal d + Matrix.vecMulVec (p.insertNth 0 v) (p.insertNth 0 v)
  let e := finOneSumSuccAboveEquiv p
  have hcross : ∀ j : Fin n, A (e (Sum.inl 0)) (e (Sum.inr j)) = 0 ∧
      A (e (Sum.inr j)) (e (Sum.inl 0)) = 0 := by
    intro j
    simp [A, e, Matrix.vecMulVec_apply, Fin.ne_succAbove,
      Fin.succAbove_ne]
  have hsub : A.submatrix (fun j => e (Sum.inr j)) (fun j => e (Sum.inr j)) =
      Matrix.diagonal (d ∘ p.succAbove) + Matrix.vecMulVec v v := by
    ext i j
    simp [A, e, Matrix.diagonal_apply, Matrix.vecMulVec_apply, Function.comp_def]
  have h := charpoly_eq_mul_of_isolated_equiv A e hcross
  rw [hsub] at h
  simpa only [A, e, finOneSumSuccAboveEquiv_inl, Matrix.add_apply,
    Matrix.diagonal_apply_eq, Matrix.vecMulVec_apply, Fin.insertNth_apply_same,
    zero_mul, add_zero] using h

/-- Inserting a zero coupling in a bordered diagonal matrix restores an
uncoupled scalar characteristic factor. The border scalar is preserved.
Horn–Johnson 2013, Theorem 4.3.21; repeated-root restoration helper. -/
theorem charpoly_bordered_diagonal_insertNth {n : ℕ}
    (d : Fin (n + 1) → ℝ) (p : Fin (n + 1)) (v : Fin n → ℝ) (a : ℝ) :
    (Matrix.fromBlocks (Matrix.diagonal d)
      (Matrix.replicateCol (Fin 1) (p.insertNth 0 v))
      (Matrix.replicateRow (Fin 1) (p.insertNth 0 v))
      (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
      (X - C (d p)) *
        (Matrix.fromBlocks (Matrix.diagonal (d ∘ p.succAbove))
          (Matrix.replicateCol (Fin 1) v) (Matrix.replicateRow (Fin 1) v)
          (Matrix.of (fun _ _ : Fin 1 => a))).charpoly := by
  let A := Matrix.fromBlocks (Matrix.diagonal d)
    (Matrix.replicateCol (Fin 1) (p.insertNth 0 v))
    (Matrix.replicateRow (Fin 1) (p.insertNth 0 v)) (Matrix.of (fun _ _ : Fin 1 => a))
  let e : Fin 1 ⊕ (Fin n ⊕ Fin 1) ≃ Fin (n + 1) ⊕ Fin 1 :=
    (Equiv.sumAssoc (Fin 1) (Fin n) (Fin 1)).symm.trans
      (Equiv.sumCongr (finOneSumSuccAboveEquiv p) (Equiv.refl (Fin 1)))
  have he0 : e (Sum.inl 0) = Sum.inl p := rfl
  have hel (i : Fin n) : e (Sum.inr (Sum.inl i)) = Sum.inl (p.succAbove i) := rfl
  have her (i : Fin 1) : e (Sum.inr (Sum.inr i)) = Sum.inr i := rfl
  have hcross : ∀ j : Fin n ⊕ Fin 1, A (e (Sum.inl 0)) (e (Sum.inr j)) = 0 ∧
      A (e (Sum.inr j)) (e (Sum.inl 0)) = 0 := by
    intro j
    cases j with
    | inl j => simp [he0, hel, A, Fin.ne_succAbove, Fin.succAbove_ne]
    | inr j => simp [he0, her, A]
  have hsub : A.submatrix (fun j => e (Sum.inr j)) (fun j => e (Sum.inr j)) =
      Matrix.fromBlocks (Matrix.diagonal (d ∘ p.succAbove))
        (Matrix.replicateCol (Fin 1) v) (Matrix.replicateRow (Fin 1) v)
        (Matrix.of (fun _ _ : Fin 1 => a)) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.submatrix_apply, hel, her, A, Matrix.diagonal_apply, Function.comp_def]
  have h := charpoly_eq_mul_of_isolated_equiv A e hcross
  rw [hsub] at h
  simpa only [he0, A, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq] using h

end NLAlib

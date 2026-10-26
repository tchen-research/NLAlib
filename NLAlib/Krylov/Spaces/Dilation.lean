import NLAlib.Krylov.Spaces.Grade
import NLAlib.Matrix.Basic.Dilation
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Krylov grades of a symmetric dilation

Even powers of the dilation act on the left normal matrix, and odd powers act on
the right normal matrix. Independent power families in the two disjoint coordinate
blocks therefore give a lower bound for the dilation grade.
Source: Golub--Van Loan (2013), Section 10.4.1; Paige--Saunders (1982), Section 3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

private theorem dilation_mulVec_inl (A : Matrix m n ℝ) (u : m → ℝ) :
    dilation A *ᵥ Sum.elim u (0 : n → ℝ) = Sum.elim (0 : m → ℝ) (Aᵀ *ᵥ u) := by
  ext (i | i) <;> simp [dilation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem dilation_mulVec_inr (A : Matrix m n ℝ) (v : n → ℝ) :
    dilation A *ᵥ Sum.elim (0 : m → ℝ) v = Sum.elim (A *ᵥ v) (0 : n → ℝ) := by
  ext (i | i) <;> simp [dilation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

variable [DecidableEq m] [DecidableEq n]

/-- Even powers of the dilation act on the left normal matrix. -/
theorem pow_dilation_mulVec_even (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    (dilation A) ^ (2 * j) *ᵥ Sum.elim b (0 : n → ℝ) =
      Sum.elim ((A * Aᵀ) ^ j *ᵥ b) (0 : n → ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [he, pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec, ih,
      dilation_mulVec_inl, dilation_mulVec_inr, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- Odd powers of the dilation act on the right normal matrix with starting vector
`Aᵀb`. -/
theorem pow_dilation_mulVec_odd (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    (dilation A) ^ (2 * j + 1) *ᵥ Sum.elim b (0 : n → ℝ) =
      Sum.elim (0 : m → ℝ) ((Aᵀ * A) ^ j *ᵥ (Aᵀ *ᵥ b)) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec, pow_dilation_mulVec_even,
    dilation_mulVec_inl, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 2
  exact (pow_mul_eq_mul_pow_of_mul_eq (by simp only [Matrix.mul_assoc]) j).symm

/-- The two independent normal-matrix power families occupy disjoint blocks of the
dilation Krylov space. Thus grades at least `q` on both sides give dilation grade at
least `2q`, including `q = 0`. -/
theorem two_mul_le_krylovGrade_dilation {A : Matrix m n ℝ} {b : m → ℝ} {q : ℕ}
    (hleft : q ≤ krylovGrade (A * Aᵀ) b)
    (hright : q ≤ krylovGrade (Aᵀ * A) (Aᵀ *ᵥ b)) :
    2 * q ≤ krylovGrade (dilation A) (Sum.elim b (0 : n → ℝ)) := by
  let u : Fin q → m → ℝ := fun j => (A * Aᵀ) ^ (j : ℕ) *ᵥ b
  let v : Fin q → n → ℝ := fun j => (Aᵀ * A) ^ (j : ℕ) *ᵥ (Aᵀ *ᵥ b)
  let w : Fin q ⊕ Fin q → m ⊕ n → ℝ :=
    Sum.elim (fun j => Sum.elim (u j) (0 : n → ℝ))
      (fun j => Sum.elim (0 : m → ℝ) (v j))
  have hu : LinearIndependent ℝ u :=
    (linearIndependent_pow_mulVec_iff_le_krylovGrade _ _).2 hleft
  have hv : LinearIndependent ℝ v :=
    (linearIndependent_pow_mulVec_iff_le_krylovGrade _ _).2 hright
  have hw : LinearIndependent ℝ w := by
    let e := (LinearEquiv.sumArrowLequivProdArrow m n ℝ ℝ).symm
    have h := (linearIndependent_inl_union_inr' hu hv).map' e.toLinearMap e.ker
    convert h using 1 <;> first | rfl | (funext j; cases j <;> rfl)
  have hle : Submodule.span ℝ (Set.range w) ≤
      krylovSpace (dilation A) (Sum.elim b (0 : n → ℝ)) (2 * q) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j | j, rfl⟩
    · change Sum.elim ((A * Aᵀ) ^ (j : ℕ) *ᵥ b) (0 : n → ℝ) ∈ _
      rw [← pow_dilation_mulVec_even]
      exact pow_mulVec_mem_krylovSpace _ _ (by omega)
    · change Sum.elim (0 : m → ℝ) ((Aᵀ * A) ^ (j : ℕ) *ᵥ (Aᵀ *ᵥ b)) ∈ _
      rw [← pow_dilation_mulVec_odd]
      exact pow_mulVec_mem_krylovSpace _ _ (by omega)
  have hd := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hw, Fintype.card_sum, Fintype.card_fin,
    finrank_krylovSpace] at hd
  omega

end NLAlib

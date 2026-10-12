import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# A diagonal determinant update and its unchanged cofactor

Replacing one diagonal entry is affine with the corresponding diagonal
cofactor. That cofactor depends only on the complementary rows and columns.
Gu–Eisenstat 1996, maximum-volume column exchange calculation.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

/-- A diagonal cofactor depends only on entries outside its deleted row and
column. This permutation proof includes one-dimensional matrices, whose
complementary determinant is empty. Supports `rank-revealing-qr`. -/
theorem det_updateCol_single_eq_of_complement_eq {p : Type*}
    [Fintype p] [DecidableEq p] (A B : Matrix p p ℝ) (i : p)
    (h : ∀ a b, a ≠ i → b ≠ i → A a b = B a b) :
    (A.updateCol i (Pi.single i 1)).det = (B.updateCol i (Pi.single i 1)).det := by
  simp only [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ i = i
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp [hσ]
    · have hσj : σ j ≠ i := fun he => hj (σ.injective (he.trans hσ.symm))
      simp only [Matrix.updateCol_apply, if_neg hj]
      exact h (σ j) j hσj hj
  · have hAz : (∏ j, (A.updateCol i (Pi.single i 1)) (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hσ])
    have hBz : (∏ j, (B.updateCol i (Pi.single i 1)) (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hσ])
    rw [hAz, hBz]

/-- Adding a scalar to one diagonal entry changes the determinant by that
scalar times its diagonal cofactor, with no invertibility hypothesis.
Supports the exact Gu–Eisenstat maximum-volume exchange identity. -/
theorem det_add_single_diagonal {p : Type*} [Fintype p] [DecidableEq p]
    (A : Matrix p p ℝ) (i : p) (a : ℝ) :
    (A + Matrix.single i i a).det = A.det + a * (A.updateCol i (Pi.single i 1)).det := by
  have heq : A + Matrix.single i i a = A.updateCol i ((fun j => A j i) + a • Pi.single i 1) := by
    ext j k
    by_cases hk : k = i
    · subst k
      simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    · simp [hk, Ne.symm hk]
  rw [heq, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  congr 1
  exact congrArg Matrix.det (Matrix.updateCol_eq_self A i)

/-- At an invertible matrix, the diagonal cofactor is determinant times the
corresponding inverse diagonal entry. Supports `rank-revealing-qr`. -/
theorem det_updateCol_single_eq_det_mul_inv {p : Type*} [Fintype p] [DecidableEq p]
    (A : Matrix p p ℝ) (hA : IsUnit A.det) (i : p) :
    (A.updateCol i (Pi.single i 1)).det = A.det * A⁻¹ i i := by
  have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (Pi.single i 1) hA) i
  simpa [Matrix.cramer_apply, Matrix.mulVec_single] using h.symm

end NLAlib

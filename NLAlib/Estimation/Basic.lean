import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Quadratic forms

`NLAlib.quadForm A z = zᵀ A z`, the estimator of Hutchinson's trace estimator (and of the
diagonal and quadratic-form estimators built from it), with its expansion as a double sum.
The theorems about it are in `NLAlib.Estimation.Hutchinson`.

Atlas: `hutchinson-unbiased`, `hutchinson-variance` (definition used in their statements).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The quadratic form `zᵀ A z`. Atlas: `hutchinson-unbiased`, `hutchinson-variance`. -/
def quadForm (A : Matrix n n ℝ) (z : n → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

/-- `0ᵀ A 0 = 0` (`@[simp]`). Atlas: `hutchinson-unbiased` (helper). -/
@[simp] theorem quadForm_zero_right (A : Matrix n n ℝ) : quadForm A 0 = 0 := by
  simp [quadForm]

/-- Expansion `zᵀ A z = ∑ᵢ ∑ⱼ A_ij z_i z_j`. Atlas: `hutchinson-unbiased` (helper). -/
theorem quadForm_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z = ∑ i, ∑ j, A i j * (z i * z j) := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end NLAlib

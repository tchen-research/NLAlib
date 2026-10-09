import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Quadratic forms and trace estimation

`NLAlib.quadForm A z = zᵀ A z`. Hutchinson's estimator is the quadratic form at an isotropic
random vector; its unbiasedness and variance are atlas targets `hutchinson-unbiased`,
`hutchinson-variance`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The quadratic form `zᵀ A z`. -/
def quadForm (A : Matrix n n ℝ) (z : n → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

@[simp] theorem quadForm_zero_right (A : Matrix n n ℝ) : quadForm A 0 = 0 := by
  simp [quadForm]

end NLAlib

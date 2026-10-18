import NLAlib.ForMathlib.Analysis.Matrix.QuadraticPositiveMap

/-! # Invertibility from a positive imaginary part

Strict positivity of the native imaginary part excludes a nonzero matrix
kernel. This connects inverse and polynomial formulations without assuming
an additional invertibility hypothesis.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix with positive definite imaginary part is invertible. -/
theorem isUnit_of_posDef_imaginaryPart {A : Matrix n n ℂ}
    (hA : (imaginaryPart A : Matrix n n ℂ).PosDef) : IsUnit A := by
  apply mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hne
  have hp := (RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hne))).1
  have hz : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hi : (matrixQuadraticFormCLM (x - y) A).im = 0 := by
    simp only [matrixQuadraticFormCLM_apply, hz, dotProduct_zero, Complex.zero_im]
  rw [im_matrixQuadraticFormCLM] at hi
  change matrixRealQuadraticFormCLM (x - y) (imaginaryPart A : Matrix n n ℂ) = 0 at hi
  change 0 < matrixRealQuadraticFormCLM (x - y) (imaginaryPart A : Matrix n n ℂ) at hp
  linarith

/-- For a positive-imaginary matrix the usual inverse equation implies
the polynomial negative-right-inverse identity. -/
theorem mul_eq_neg_one_of_neg_inv_eq_of_posDef_imaginaryPart
    {A T : Matrix n n ℂ} (hA : (imaginaryPart A : Matrix n n ℂ).PosDef)
    (heq : -A⁻¹ = T) : T * A = -1 := by
  rw [← heq, neg_mul, nonsing_inv_mul A ((isUnit_iff_isUnit_det A).mp
    (isUnit_of_posDef_imaginaryPart hA))]

end Matrix

import NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Positive matrix quadratic maps

The scalar quadratic probe is a positive complex-linear map. Native
positive-map star preservation therefore transports the matrix imaginary
part to the scalar imaginary part exactly.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule

/-- The imaginary self-adjoint part of a complex number is its imaginary
coordinate embedded into the complex numbers. -/
theorem Complex.coe_imaginaryPart (z : ℂ) : (imaginaryPart z : ℂ) = (z.im : ℂ) := by
  rw [imaginaryPart_apply_coe]
  apply Complex.ext <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
  ring

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A fixed-vector matrix quadratic probe as a positive complex-linear map. -/
def matrixQuadraticPositiveMap (v : n → ℂ) : Matrix n n ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixQuadraticFormCLM v).toLinearMap
    (fun _ hA => hA.posSemidef.dotProduct_mulVec_nonneg v)

omit [DecidableEq n] in
@[simp] theorem matrixQuadraticPositiveMap_apply (v : n → ℂ) (A : Matrix n n ℂ) :
    matrixQuadraticPositiveMap v A = matrixQuadraticFormCLM v A := rfl

/-- Scalar imaginary quadratic forms are the real quadratic forms of
the native matrix imaginary part. -/
theorem im_matrixQuadraticFormCLM (v : n → ℂ) (A : Matrix n n ℂ) :
    (matrixQuadraticFormCLM v A).im =
      matrixRealQuadraticFormCLM v (imaginaryPart A : Matrix n n ℂ) := by
  have h := map_imaginaryPart (matrixQuadraticPositiveMap v) A
  rw [Complex.coe_imaginaryPart] at h
  exact (congrArg Complex.re h).symm

/-- Positive semidefinite matrix imaginary part gives nonnegative scalar
imaginary part for every deterministic quadratic probe. -/
theorem im_matrixQuadraticFormCLM_nonneg (v : n → ℂ) (A : Matrix n n ℂ)
    (hA : Matrix.PosSemidef (imaginaryPart A : Matrix n n ℂ)) :
    0 ≤ (matrixQuadraticFormCLM v A).im := by
  rw [im_matrixQuadraticFormCLM]
  exact hA.re_dotProduct_nonneg v

end Matrix

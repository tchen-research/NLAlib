import NLAlib.Matrix.Perturbation.ResidualBounds
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Rayleigh quotient gradient

For a real symmetric matrix, the gradient is twice the Rayleigh residual
divided by the squared vector norm. The nonzero-vector condition remains
explicit. Source: Parlett §4.5; atlas `eigenvalue-residual-bounds`.
-/

noncomputable section
open scoped Matrix RealInnerProductSpace

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Fréchet derivative of the Rayleigh quotient is the inner product
with its residual gradient. Parlett §4.5; the vector must be nonzero.
atlas: eigenvalue-residual-bounds -/
theorem hasFDerivAt_rayleighQuotient (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ n) (hx : x ≠ 0) :
    HasFDerivAt (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
      (innerSL ℝ ((2/‖x‖^2) • (Matrix.toEuclideanCLM (𝕜 := ℝ) A x -
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient x • x))) x := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hsym : (T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hnum := hsym.hasStrictFDerivAt_reApplyInnerSelf x |>.hasFDerivAt
  have hden := hasStrictFDerivAt_norm_sq x |>.hasFDerivAt
  have hn : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hh := hnum.mul ((hasFDerivAt_inv hn).comp x hden)
  convert! hh using 1
  ext y
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, real_inner_smul_left, inner_sub_left,
    ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Function.comp_apply, T]
  field_simp
  ring

end NLAlib

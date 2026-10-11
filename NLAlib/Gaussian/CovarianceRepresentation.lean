import NLAlib.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Covariance representation of a general centered Gaussian vector

Every centered Gaussian law, including singular covariance, is the canonical
multivariate law and hence a linear image of independent standard coordinates.
Source: operator re-derivation `pg:gaussian-linear-image`.
Supports atlas `isserlis` and `rotation-invariance`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- The covariance matrix of a Euclidean vector law, in the standard basis.
For a centered Gaussian it equals the coordinate product expectations.
Source: operator re-derivation `pg:gaussian-linear-image`. -/
def gaussianCovarianceMatrix {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (covarianceBilin μ).toBilinForm

/-- The covariance matrix is positive semidefinite, allowing zero eigenvalues.
Source: covariance is a nonnegative symmetric bilinear form; operator
re-derivation `pg:gaussian-linear-image`. -/
theorem gaussianCovarianceMatrix_posSemidef {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : (gaussianCovarianceMatrix μ).PosSemidef := by
  exact (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).mp
      (LinearMap.BilinForm.isPosSemidef_iff.mp isPosSemidef_covarianceBilin)

/-- Covariance matrix entries are covariances of the coordinate maps.
Source: the standard Euclidean basis; operator re-derivation `pg:gaussian-linear-image`. -/
theorem gaussianCovarianceMatrix_apply {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (i j : Fin n) :
    gaussianCovarianceMatrix μ i j = cov[fun x => x i, fun x => x j; μ] := by
  rw [gaussianCovarianceMatrix, LinearMap.toMatrix₂_apply]
  rw [ContinuousLinearMap.toBilinForm_apply, covarianceBilin_apply_eq_cov hμ]
  simp [PiLp.inner_apply]

/-- An arbitrary centered Gaussian law is its canonical covariance law.
No inverse covariance or nonsingularity assumption is used.
Source: operator re-derivation `pg:gaussian-linear-image`, Gaussian uniqueness
from mean and covariance. -/
theorem gaussian_eq_multivariateGaussian_covariance_of_centered {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) :
    μ = multivariateGaussian 0 (gaussianCovarianceMatrix μ) := by
  apply IsGaussian.ext
  · simpa only [id_eq, integral_id_multivariateGaussian] using hmean
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    intro i j
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_multivariateGaussian (gaussianCovarianceMatrix_posSemidef μ)]
    simp [gaussianCovarianceMatrix, LinearMap.toMatrix₂_apply, dotProduct, Matrix.mulVec,
      EuclideanSpace.basisFun_apply]

/-- A general centered Gaussian law is the image of independent standard
coordinates under the positive covariance square root, including singular
and zero-dimensional laws. Source: operator re-derivation `pg:gaussian-linear-image`. -/
theorem gaussian_eq_map_pi_sqrt_covariance_of_centered {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) :
    μ = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
      (fun x => WithLp.toLp 2 (CFC.sqrt (gaussianCovarianceMatrix μ) *ᵥ x)) := by
  calc
    μ = multivariateGaussian 0 (gaussianCovarianceMatrix μ) :=
      gaussian_eq_multivariateGaussian_covariance_of_centered μ hmean
    _ = _ := by
      rw [multivariateGaussian]
      rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      simp only [Function.comp_def, zero_add, Matrix.toEuclideanCLM_toLp]

end NLAlib

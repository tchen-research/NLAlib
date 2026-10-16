import NLAlib.RandomMatrix.Gaussian.Comparison.CauchyInterpolation
import NLAlib.Probability.Gaussian.Comparison.MatrixCauchyEndpoints
import NLAlib.Probability.Moments.MatrixDifferenceBound

/-! # Cauchy universality for actual Hermitian matrix laws

Independent matrix summands with finite third norm moments and a genuine
Gaussian Hermitian matrix with the same actual mean and full real-entry
covariance have normalized trace resolvents within M3 / |Im ζ|⁴. A centered
spectral bound gives the exact 4 L sigma² / |Im ζ|⁴ consequence. The proof
uses the checked actual coordinate interpolation and reconstructs both
endpoints and the original independent-copy moment parameter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- Sharp Cauchy-transform comparison for actual independent Hermitian matrix
laws and a genuine matching Gaussian Hermitian matrix law. The covariance
hypothesis retains all real and imaginary entries and every mixed covariance;
matching only the matrix second moment is not sufficient. No conditional
expectation, interpolation derivative, or remainder interface is assumed.
Source: supplied probability reroute, Cauchy comparison-main.
atlas: cauchy-transform-gaussian-universality (partial)
-/
theorem norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_matrixDifferenceThirdMoment
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : M → M) 3 (ν i))
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ)
    (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (hmean : (∫ A : M, A ∂ρ) = ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b); ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ‖(∫ x : ι → M, normalizedTrace (resolvent (∑ i, x i) ζ) ∂Measure.pi ν) -
      ∫ A : M, normalizedTrace (resolvent A ζ) ∂ρ‖ ≤
      matrixDifferenceThirdMoment ν / |ζ.im|^4 := by
  letI : MeasurableSpace ι := ⊤
  haveI (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  let γ := centeredMatrixCoordinateLaw ρ
  have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
  haveI := hγ.isProbabilityMeasure
  have hh := norm_resamplingInterpolation_trace_resolvent_sub_le_matrixDifferenceThirdMoment
    (fun i => (ν i).map matrixRealCoordinates)
    (fun i => memLp_id_map_matrixRealCoordinates (ν i) (hν i)) γ hγ
    (fun a => integral_eval_centeredMatrixCoordinateLaw_eq_zero ρ hρ a)
    (fun a b => (covariance_eval_centeredMatrixCoordinateLaw ρ hρ a b).trans
      ((hcov a b).trans (covariance_resamplingTripleOriginal_matrixRealCoordinates ν a b).symm)) ζ hζ
  rw [resamplingInterpolation_one_matrix_law ν hHerm γ ζ hζ,
    resamplingInterpolation_zero_matrix_law ν hν ρ hρ hρHerm hmean ζ hζ,
    matrixDifferenceThirdMoment_map_matrixRealCoordinates_reconstruct ν hHerm] at hh
  exact hh

open scoped Matrix.Norms.L2Operator in
/-- The bounded-summand Cauchy consequence with exact constant four and the
actual centered variance matrix. All required third moments follow from the
centered spectral bound; zero bound and zero variance are included.
Source: supplied probability reroute, bounded-summands paragraph.
atlas: cauchy-transform-gaussian-universality (partial)
-/
theorem norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_four_mul_bound_mul_variance
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ)
    (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (hmean : (∫ A : M, A ∂ρ) = ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b); ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ i, ∀ᵐ A ∂ν i, specNorm (A - ∫ B : M, B ∂ν i) ≤ L)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ‖(∫ x : ι → M, normalizedTrace (resolvent (∑ i, x i) ζ) ∂Measure.pi ν) -
      ∫ A : M, normalizedTrace (resolvent A ζ) ∂ρ‖ ≤
      (4 * L * specNorm (∑ i, ∫ A : M, (A - ∫ B : M, B ∂ν i)^2 ∂ν i)) / |ζ.im|^4 := by
  have hν (i : ι) : MemLp (id : M → M) 3 (ν i) :=
    memLp_id_of_ae_specNorm_centered_le (ν i) (hbound i)
  exact (norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_matrixDifferenceThirdMoment
    ν hν hHerm ρ hρ hρHerm hmean hcov ζ hζ).trans
      (div_le_div_of_nonneg_right
        (matrixDifferenceThirdMoment_le_four_mul_bound_mul_variance ν hL hHerm hbound)
        (by positivity))

end NLAlib

import NLAlib.RandomMatrix.Gaussian.Comparison.CauchyTransform
import NLAlib.Matrix.Functions.ResolventMeasurability

/-!
# Cauchy universality on arbitrary probability spaces

Actual marginal laws and independence transport the product-law comparison
to random matrices on any sample spaces. Only the full original mean and
covariance matching conditions are used; no additional coupling assumptions
or analytic interfaces are needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι n Ω Ω' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
private theorem measurable_normalizedTrace_resolvent (ζ : ℂ) :
    Measurable (fun A : M => normalizedTrace (resolvent A ζ)) := by
  have htr : Measurable (normalizedTrace : M → ℂ) :=
    (continuous_const.mul continuous_id.matrix_trace).measurable
  exact htr.comp (measurable_matrix_resolvent ζ)

open scoped Matrix.Norms.L2Operator in
private theorem integral_sum_resolvent_eq_of_indepFun_hasLaw
    (ν : ι → Measure M) (X : ι → Ω → M)
    (hX : ∀ i, HasLaw (X i) (ν i) P) (hXi : iIndepFun X P) (ζ : ℂ) :
    (∫ ω, normalizedTrace (resolvent (∑ i, X i ω) ζ) ∂P) =
      ∫ x : ι → M, normalizedTrace (resolvent (∑ i, x i) ζ) ∂Measure.pi ν := by
  have hm : Measurable (fun x : ι → M => normalizedTrace (resolvent (∑ i, x i) ζ)) :=
    (measurable_normalizedTrace_resolvent ζ).comp (by fun_prop)
  exact (hXi.hasLaw_pi hX).integral_comp hm.aestronglyMeasurable

open scoped Matrix.Norms.L2Operator in
private theorem integral_resolvent_eq_of_hasLaw
    (ρ : Measure M) (G : Ω' → M) (hG : HasLaw G ρ P') (ζ : ℂ) :
    (∫ ω, normalizedTrace (resolvent (G ω) ζ) ∂P') =
      ∫ A : M, normalizedTrace (resolvent A ζ) ∂ρ :=
  hG.integral_comp (measurable_normalizedTrace_resolvent ζ).aestronglyMeasurable

open scoped Matrix.Norms.L2Operator in
/-- The sharp actual Cauchy comparison transports to independent random
summands and a Gaussian comparison matrix on arbitrary sample spaces through
their actual laws. No relation between the two sample spaces is required.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_matrixDifferenceThirdMoment_of_hasLaw
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
    (X : ι → Ω → M) (hX : ∀ i, HasLaw (X i) (ν i) P) (hXi : iIndepFun X P)
    (G : Ω' → M) (hG : HasLaw G ρ P') (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ‖(∫ ω, normalizedTrace (resolvent (∑ i, X i ω) ζ) ∂P) -
      ∫ ω, normalizedTrace (resolvent (G ω) ζ) ∂P'‖ ≤
      matrixDifferenceThirdMoment ν / |ζ.im|^4 := by
  rw [integral_sum_resolvent_eq_of_indepFun_hasLaw ν X hX hXi ζ,
    integral_resolvent_eq_of_hasLaw ρ G hG ζ]
  exact norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_matrixDifferenceThirdMoment
    ν hν hHerm ρ hρ hρHerm hmean hcov ζ hζ

open scoped Matrix.Norms.L2Operator in
/-- The exact constant-four centered-bounded Cauchy consequence transports to
arbitrary sample spaces via genuine marginal laws and summand independence.
All required moments follow from the original centered spectral bound.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_four_mul_bound_mul_variance_of_hasLaw
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
    (X : ι → Ω → M) (hX : ∀ i, HasLaw (X i) (ν i) P) (hXi : iIndepFun X P)
    (G : Ω' → M) (hG : HasLaw G ρ P') (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ‖(∫ ω, normalizedTrace (resolvent (∑ i, X i ω) ζ) ∂P) -
      ∫ ω, normalizedTrace (resolvent (G ω) ζ) ∂P'‖ ≤
      (4 * L * specNorm (∑ i, ∫ A : M, (A - ∫ B : M, B ∂ν i)^2 ∂ν i)) / |ζ.im|^4 := by
  rw [integral_sum_resolvent_eq_of_indepFun_hasLaw ν X hX hXi ζ,
    integral_resolvent_eq_of_hasLaw ρ G hG ζ]
  exact norm_integral_normalizedTrace_resolvent_sum_sub_gaussian_le_four_mul_bound_mul_variance
    ν hHerm ρ hρ hρHerm hmean hcov hL hbound ζ hζ

end NLAlib

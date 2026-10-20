import NLAlib.Probability.Gaussian.Comparison.ResolventMomentInterpolation
import NLAlib.Probability.Transforms.ResolventMoments

/-!
# Actual real resolvent moments along resampling interpolation

The genuine real Gram-moment path is continuous, agrees with the real part
of the complex mixed-trace interpolation, and is strictly positive in
nonempty dimension. These facts justify rooted endpoint comparison.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)
local notation "Q" => (ι × ((ι × Fin 3) → E)) × E

open scoped Matrix.Norms.L2Operator in
/-- The actual normalized Gram-moment interpolation is continuous at every
time, including the two endpoints of the unit interval. -/
theorem continuous_resamplingInterpolation_resolventEvenMoment
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) [IsProbabilityMeasure γ]
    (A : M) (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) :
    Continuous (resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p)) := by
  apply continuous_resamplingInterpolation ν hν γ _
    (contDiff_resolventEvenMoment_coordinate A hA ζ hζ p (r := ⊤)).continuous
    ((|ζ.im|⁻¹) ^ (2 * p))
  intro x
  rw [Real.norm_of_nonneg (resolventEvenMoment_nonneg _ ζ hp)]
  exact resolventEvenMoment_le_inv_abs_im_pow _
    (hA.add (isHermitian_hermitianMatrixFromRealCoordinates x)) hζ hp

omit [DecidableEq ι] [MeasurableSingletonClass ι] in
open scoped Matrix.Norms.L2Operator in
/-- Real Gram-moment interpolation is the real part of the actual complex
mixed-trace interpolation. The complex integrand is integrable by its native
uniform resolvent bound. -/
theorem resamplingInterpolation_resolventEvenMoment_eq_re
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure E) [IsProbabilityMeasure γ]
    (A : M) (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) (p : ℕ) (t : ℝ) :
    resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p) t =
      (resamplingInterpolation ν γ (fun x => normalizedTrace
        (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) t).re := by
  let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
  let Y : Q → E := fun q => resamplingAffinePoint μ (Real.sqrt t)
    (Real.sqrt (1 - t)) (resamplingTripleOriginal q.1) q.2
  let Φ : E → ℂ := fun x => normalizedTrace
    (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)
  have hY : Measurable Y := by
    unfold Y resamplingAffinePoint resamplingTripleOriginal
    fun_prop
  have hΦ : Continuous Φ :=
    (contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p (r := ⊤)).continuous
  have hi : Integrable (fun q => Φ (Y q)) ((resamplingTripleMeasure ν).prod γ) :=
    Integrable.of_bound (hΦ.measurable.comp hY).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun q =>
        norm_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p (Y q))
  change (∫ q, resolventEvenMoment (A + L (Y q)) ζ p
    ∂(resamplingTripleMeasure ν).prod γ) = (∫ q, Φ (Y q)
    ∂(resamplingTripleMeasure ν).prod γ).re
  calc
    _ = ∫ q, (Φ (Y q)).re ∂(resamplingTripleMeasure ν).prod γ := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact resolventEvenMoment_eq_re_normalizedTrace_mul_pow
        (hA.add (isHermitian_hermitianMatrixFromRealCoordinates (Y q))) ζ p
    _ = _ := Complex.reCLM.integral_comp_comm hi

omit [DecidableEq ι] [MeasurableSingletonClass ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual real Gram-moment interpolation is strictly positive at every
time in nonempty matrix dimension, with no Gaussian or covariance assumptions. -/
theorem resamplingInterpolation_resolventEvenMoment_pos [Nonempty n]
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure E) [IsProbabilityMeasure γ]
    (A : M) (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    0 < resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p) t := by
  let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
  let Y : Q → E := fun q => resamplingAffinePoint μ (Real.sqrt t)
    (Real.sqrt (1 - t)) (resamplingTripleOriginal q.1) q.2
  have hY : Measurable Y := by
    unfold Y resamplingAffinePoint resamplingTripleOriginal
    fun_prop
  change 0 < ∫ q, resolventEvenMoment (A + L (Y q)) ζ p
    ∂(resamplingTripleMeasure ν).prod γ
  apply integral_resolventEvenMoment_pos ((resamplingTripleMeasure ν).prod γ)
    (fun q => A + L (Y q))
  · exact (measurable_const.add ((L).continuous.measurable.comp hY)).aemeasurable
  · exact Filter.Eventually.of_forall fun q =>
      hA.add (isHermitian_hermitianMatrixFromRealCoordinates (Y q))
  · exact hζ
  · exact hp

end NLAlib

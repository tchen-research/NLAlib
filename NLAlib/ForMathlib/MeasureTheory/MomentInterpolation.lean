import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive real moment comparison

On a probability space, the rooted positive real moments of a nonnegative
measurable function increase with the exponent. These estimates also hold
when an exponent is less than one; no norm terminology is needed.

The statements support the quadratic-probe operator proof of inverse
Gaussian moments. Atlas: `inverse-wishart-spectral-moment`,
`pinv-spectral-expectation`.
-/

noncomputable section

open MeasureTheory

namespace NLAlib

/-- A lower positive real moment is integrable whenever a higher one is.
Source: moment monotonicity in the direct quadratic-probe proof.
Atlas: `inverse-wishart-spectral-moment` (helper); allows exponents below one.
atlas: positive-real-moment-comparison -/
theorem integrable_rpow_of_nonneg_of_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {p q : ℝ}
    (hf : AEStronglyMeasurable f μ) (hfnn : ∀ ω, 0 ≤ f ω)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ≤ q)
    (hfq : Integrable (fun ω => f ω ^ q) μ) :
    Integrable (fun ω => f ω ^ p) μ := by
  have hnorm : ∀ ω, ‖f ω‖ = f ω := fun ω => Real.norm_of_nonneg (hfnn ω)
  have hfq' : Integrable (fun ω => ‖f ω‖ ^ q) μ := by simpa only [hnorm] using hfq
  simpa only [hnorm] using integrable_norm_rpow_of_le hf hp hq hpq hfq'

/-- Rooted moments are monotone for all positive real exponents on a
probability space. Source: moment monotonicity in the direct quadratic-probe
proof. Atlas: `inverse-wishart-spectral-moment` (helper); includes `p < 1`.
atlas: positive-real-moment-comparison -/
theorem integral_rpow_root_le_of_nonneg_of_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {p q : ℝ}
    (hf : AEStronglyMeasurable f μ) (hfnn : ∀ ω, 0 ≤ f ω)
    (hp : 0 < p) (hpq : p ≤ q) (hfq : Integrable (fun ω => f ω ^ q) μ) :
    (∫ ω, f ω ^ p ∂μ) ^ p⁻¹ ≤ (∫ ω, f ω ^ q ∂μ) ^ q⁻¹ := by
  have hq : 0 < q := hp.trans_le hpq
  have hnorm : ∀ ω, ‖f ω‖ = f ω := fun ω => Real.norm_of_nonneg (hfnn ω)
  have hfp := integrable_rpow_of_nonneg_of_le hf hfnn hp.le hq.le hpq hfq
  have hMp : MemLp f (ENNReal.ofReal p) μ :=
    (integrable_norm_rpow_iff hf (by simp [hp]) (by simp)).1
      (by simpa only [ENNReal.toReal_ofReal hp.le, hnorm] using hfp)
  have hMq : MemLp f (ENNReal.ofReal q) μ :=
    (integrable_norm_rpow_iff hf (by simp [hq]) (by simp)).1
      (by simpa only [ENNReal.toReal_ofReal hq.le, hnorm] using hfq)
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hf
  rw [hMp.eLpNorm_eq_integral_rpow_norm (by simp [hp]) (by simp),
    hMq.eLpNorm_eq_integral_rpow_norm (by simp [hq]) (by simp)] at hmono
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, hnorm] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg
    (integral_nonneg fun ω => Real.rpow_nonneg (hfnn ω) _) _)).1 hmono

/-- A bound on one positive real moment bounds every lower rooted moment.
Source: moment monotonicity in the direct quadratic-probe proof.
Atlas: `inverse-wishart-spectral-moment`, `pinv-spectral-expectation`
(helper); neither exponent needs to be at least one.
atlas: positive-real-moment-comparison -/
theorem integral_rpow_root_le_of_integral_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {p q C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hfnn : ∀ ω, 0 ≤ f ω)
    (hp : 0 < p) (hpq : p ≤ q) (hC : 0 ≤ C)
    (hfq : Integrable (fun ω => f ω ^ q) μ) (hqbound : (∫ ω, f ω ^ q ∂μ) ≤ C ^ q) :
    (∫ ω, f ω ^ p ∂μ) ^ p⁻¹ ≤ C := by
  have hq : 0 < q := hp.trans_le hpq
  calc (∫ ω, f ω ^ p ∂μ) ^ p⁻¹ ≤ (∫ ω, f ω ^ q ∂μ) ^ q⁻¹ :=
      integral_rpow_root_le_of_nonneg_of_le hf hfnn hp hpq hfq
    _ ≤ (C ^ q) ^ q⁻¹ := Real.rpow_le_rpow
      (integral_nonneg fun ω => Real.rpow_nonneg (hfnn ω) _) hqbound (by positivity)
    _ = C := Real.rpow_rpow_inv hC hq.ne'

/-- A bound `E[f^q] ≤ C^q` implies integrability and `E[f^p] ≤ C^p`
for every real `0 < p ≤ q`. Source: moment monotonicity in the direct
quadratic-probe proof. Atlas: `inverse-wishart-spectral-moment`,
`pinv-spectral-expectation` (helper); includes exponents below one.
atlas: positive-real-moment-comparison -/
theorem integrable_and_integral_rpow_le_of_integral_rpow_le {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p q C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hfnn : ∀ ω, 0 ≤ f ω)
    (hp : 0 < p) (hpq : p ≤ q) (hC : 0 ≤ C)
    (hfq : Integrable (fun ω => f ω ^ q) μ) (hqbound : (∫ ω, f ω ^ q ∂μ) ≤ C ^ q) :
    Integrable (fun ω => f ω ^ p) μ ∧ (∫ ω, f ω ^ p ∂μ) ≤ C ^ p := by
  have hq : 0 < q := hp.trans_le hpq
  refine ⟨integrable_rpow_of_nonneg_of_le hf hfnn hp.le hq.le hpq hfq, ?_⟩
  have hroot := integral_rpow_root_le_of_integral_rpow_le hf hfnn hp hpq hC hfq hqbound
  have hpint : 0 ≤ ∫ ω, f ω ^ p ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (hfnn ω) _
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hpint _) hroot hp.le
  rwa [Real.rpow_inv_rpow hpint hp.ne'] at h

end NLAlib

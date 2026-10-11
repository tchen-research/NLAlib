import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# First and second moments from a half-rate exponential tail

Nonnegative tail integration gives moments two and eight before asserting
integrability. Source: manuscript `rt:log-moments`, scalar tail integration.
-/

noncomputable section
open MeasureTheory Set
namespace NLAlib

private theorem lintegral_ofReal_exp_neg_half_Ioi_eq_two :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t / 2))) = ENNReal.ofReal 2 := by
  have he : (fun t : ℝ => Real.exp (-t / 2)) = fun t => Real.exp ((-1 / 2 : ℝ) * t) := by
    funext t
    congr 1
    ring
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
    rw [he]
    exact integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    he, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
  norm_num

private theorem lintegral_ofReal_two_mul_mul_exp_neg_half_Ioi_eq_eight :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (2 * t * Real.exp (-t / 2))) = ENNReal.ofReal 8 := by
  have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 1 / 2) (by norm_num) (by norm_num)
  have hgamma : Real.Gamma 2 = 1 := by
    norm_num
  have he : (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-((1 / 2) * t))) =
      fun t => t * Real.exp (-t / 2) := by
    funext t
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    congr 2
    ring
  rw [he, hgamma] at hG
  norm_num at hG
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-t / 2)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hG]; norm_num)
  have hi2 : IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-t / 2)) (Ioi 0) := by
    have he2 : (fun t : ℝ => 2 * t * Real.exp (-t / 2)) =
        fun t => 2 * (t * Real.exp (-t / 2)) := by funext t; ring
    rw [he2]
    exact hi.const_mul 2
  rw [← ofReal_integral_eq_lintegral_ofReal hi2]
  · have he2 : (fun t : ℝ => 2 * t * Real.exp (-t / 2)) =
        fun t => 2 * (t * Real.exp (-t / 2)) := by funext t; ring
    rw [he2, integral_const_mul, hG]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht.le) (Real.exp_pos _).le

/-- A nonnegative measurable variable with tail `P{f>t} ≤ exp(-t/2)` has integrable
first and second moments, bounded by two and eight. Source: manuscript `rt:log-moments`;
layer-cake integration is applied before integrability is claimed. -/
theorem integrable_and_integral_sq_le_of_exp_neg_half_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (htail : ∀ t : ℝ, 0 < t → μ {ω | t < f ω} ≤ ENNReal.ofReal (Real.exp (-t / 2))) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ 2 ∧
      Integrable (fun ω => f ω ^ 2) μ ∧ (∫ ω, f ω ^ 2 ∂μ) ≤ 8 := by
  have hL : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal 2 := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hf0) hf.aemeasurable]
    calc (∫⁻ t : ℝ in Ioi 0, μ {ω | t < f ω}) ≤
        ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t / 2)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact htail t ht
      _ = _ := lintegral_ofReal_exp_neg_half_Ioi_eq_two
  have hInt : ∀ z : ℝ, (∫ t in 0..z, 2 * t) = z ^ 2 := by
    intro z
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hLC := lintegral_comp_eq_lintegral_meas_lt_mul μ (ae_of_all _ hf0) hf.aemeasurable
    (g := fun t : ℝ => 2 * t)
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (by norm_num) ht.le)
  simp only [hInt] at hLC
  have hL2 : (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ) ≤ ENNReal.ofReal 8 := by
    rw [hLC]
    calc (∫⁻ t : ℝ in Ioi 0, μ {ω | t < f ω} * ENNReal.ofReal (2 * t)) ≤
        ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (2 * t) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_le_mul_of_nonneg_right (htail t ht) (by positivity)
      _ = ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (2 * t * Real.exp (-t / 2)) := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun t => by
            change ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (2 * t) =
              ENNReal.ofReal (2 * t * Real.exp (-t / 2))
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            ring
      _ = _ := lintegral_ofReal_two_mul_mul_exp_neg_half_Ioi_eq_eight
  have hi : Integrable f μ :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).mpr
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  have hi2 : Integrable (fun ω => f ω ^ 2) μ :=
    ⟨(hf.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg (f ω))).mpr
        (hL2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_, hi2, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg (f ω))
      (hf.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL2

end NLAlib

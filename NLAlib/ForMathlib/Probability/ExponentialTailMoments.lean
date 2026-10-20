import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Moments from exponential tails

Nonnegative tail integration gives moments two and eight for a half-rate
tail and every positive integer moment for a shifted exponential tail,
before asserting integrability. Layer-cake integration
(Vershynin 2018, Lemma 1.2.1).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace MeasureTheory

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

private theorem integrable_and_integral_sq_le_of_exp_neg_half_tail
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

section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
  (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
  (htail : ∀ t : ℝ, 0 < t → μ {ω | t < f ω} ≤ ENNReal.ofReal (Real.exp (-t / 2)))
include hf hf0 htail

/-- A nonnegative measurable variable with tail `P{f > t} ≤ exp(-t/2)` is integrable
(layer-cake integration; Vershynin 2018, Lemma 1.2.1). -/
theorem integrable_of_exp_neg_half_tail : Integrable f μ :=
  (integrable_and_integral_sq_le_of_exp_neg_half_tail f hf hf0 htail).1

/-- A nonnegative variable with tail `P{f > t} ≤ exp(-t/2)` has mean at most `2`
(Vershynin 2018, Lemma 1.2.1). -/
theorem integral_le_two_of_exp_neg_half_tail : (∫ ω, f ω ∂μ) ≤ 2 :=
  (integrable_and_integral_sq_le_of_exp_neg_half_tail f hf hf0 htail).2.1

/-- A nonnegative measurable variable with tail `P{f > t} ≤ exp(-t/2)` is square integrable
(Vershynin 2018, Lemma 1.2.1). -/
theorem integrable_sq_of_exp_neg_half_tail : Integrable (fun ω => f ω ^ 2) μ :=
  (integrable_and_integral_sq_le_of_exp_neg_half_tail f hf hf0 htail).2.2.1

/-- A nonnegative variable with tail `P{f > t} ≤ exp(-t/2)` has second moment at most `8`
(Vershynin 2018, Lemma 1.2.1). -/
theorem integral_sq_le_eight_of_exp_neg_half_tail : (∫ ω, f ω ^ 2 ∂μ) ≤ 8 :=
  (integrable_and_integral_sq_le_of_exp_neg_half_tail f hf hf0 htail).2.2.2

end

end MeasureTheory

namespace MeasureTheory

/-- An actual nonnegative random variable dominated by a unit exponential tail
has every positive integer moment and its real `L^q` norm is at most `q`.
The proof uses the layer-cake identity and the exact Gamma integral. -/
theorem memLp_and_lpNorm_le_nat_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (hnn : ∀ ω, 0 ≤ X ω)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < X ω} ≤ Real.exp (-t))
    (q : ℕ) (hq : 0 < q) :
    MemLp X (q : ℝ≥0∞) μ ∧ lpNorm X (q : ℝ≥0∞) μ ≤ q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  have hqtop : (q : ℝ≥0∞) ≠ ∞ := by simp
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((q : ℝ) - 1))
      (Ioi 0) := Real.GammaIntegral_convergent hqr
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t : ℝ => Real.exp (-t) * t ^ ((q : ℝ) - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  have hGamma : (q : ℝ) * Real.Gamma q = (q.factorial : ℝ) := by
    rw [← Real.Gamma_add_one hqr.ne', Real.Gamma_nat_eq_factorial]
  have hmoment : (∫⁻ ω, ENNReal.ofReal (X ω ^ (q : ℝ)) ∂μ) ≤
      ENNReal.ofReal (q.factorial : ℝ) := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ
      (Filter.Eventually.of_forall hnn) hX hqr]
    calc
      _ ≤ ENNReal.ofReal (q : ℝ) *
          ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-t) * t ^ ((q : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal (htail t ht)
      _ = ENNReal.ofReal ((q : ℝ) * Real.Gamma q) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hg hgnn,
          ← Real.Gamma_eq_integral hqr, ← ENNReal.ofReal_mul hqr.le]
      _ = _ := by rw [hGamma]
  have hpowMeas : AEMeasurable (fun ω => X ω ^ (q : ℝ)) μ := hX.pow_const _
  have hpowNN : 0 ≤ᵐ[μ] fun ω => X ω ^ (q : ℝ) :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hnn ω) _
  have hpowInt : Integrable (fun ω => X ω ^ (q : ℝ)) μ := by
    refine ⟨hpowMeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hpowNN).2 ?_⟩
    exact hmoment.trans_lt ENNReal.ofReal_lt_top
  have hmem : MemLp X (q : ℝ≥0∞) μ := by
    apply (integrable_norm_rpow_iff hX.aestronglyMeasurable hq0 hqtop).mp
    simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
      using hpowInt
  refine ⟨hmem, ?_⟩
  have hpowLe : (∫ ω, X ω ^ (q : ℝ) ∂μ) ≤ (q.factorial : ℝ) := by
    rw [integral_eq_lintegral_of_nonneg_ae hpowNN hpowMeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg _) hmoment
  have hfac : (q.factorial : ℝ) ≤ (q : ℝ) ^ (q : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.factorial_le_pow q
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop hX.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
  calc
    _ ≤ ((q : ℝ) ^ (q : ℝ)) ^ (q : ℝ)⁻¹ :=
      Real.rpow_le_rpow (integral_nonneg_of_ae hpowNN) (hpowLe.trans hfac)
        (inv_nonneg.mpr hqr.le)
    _ = q := by rw [← Real.rpow_mul hqr.le, mul_inv_cancel₀ hqr.ne', Real.rpow_one]

/-- A shifted exponential tail gives an actual integer `L^q` norm bound.
No moment or integrability hypothesis is supplied. -/
theorem memLp_and_lpNorm_le_of_shifted_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (hnn : ∀ ω, 0 ≤ X ω)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | a + b * t < X ω} ≤ Real.exp (-t))
    (q : ℕ) (hq : 0 < q) :
    MemLp X (q : ℝ≥0∞) μ ∧ lpNorm X (q : ℝ≥0∞) μ ≤ a + b * q := by
  let Y : Ω → ℝ := fun ω => max (X ω - a) 0 / b
  have hY : AEMeasurable Y μ := ((hX.sub_const a).max aemeasurable_const).div_const b
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (le_max_right _ _) hb.le
  have hYtail : ∀ t : ℝ, 0 < t → μ.real {ω | t < Y ω} ≤ Real.exp (-t) := by
    intro t ht
    have he : {ω | t < Y ω} = {ω | a + b * t < X ω} := by
      ext ω
      change t < max (X ω - a) 0 / b ↔ _
      rw [lt_div_iff₀ hb, lt_max_iff]
      have hbt : ¬t * b < 0 := not_lt.mpr (mul_nonneg ht.le hb.le)
      simp only [hbt, or_false]
      change t * b < X ω - a ↔ a + b * t < X ω
      constructor <;> intro h <;> nlinarith
    rw [he]
    exact htail t ht
  obtain ⟨hYm, hYn⟩ := memLp_and_lpNorm_le_nat_of_exponential_tail μ Y hY hYnn hYtail q hq
  let G : Ω → ℝ := fun ω => a + b * Y ω
  have hGm : MemLp G (q : ℝ≥0∞) μ := (memLp_const a).add (hYm.const_mul b)
  have hdom : ∀ ω, ‖X ω‖ ≤ G ω := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    dsimp [G, Y]
    rw [mul_div_cancel₀ _ hb.ne']
    linarith [le_max_left (X ω - a) 0]
  have hXm : MemLp X (q : ℝ≥0∞) μ := hGm.of_le hX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => (hdom ω).trans (le_abs_self _))
  refine ⟨hXm, (lpNorm_mono_real hGm hdom).trans ?_⟩
  have hqone : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq
  calc
    lpNorm G (q : ℝ≥0∞) μ ≤ lpNorm (fun _ : Ω => a) (q : ℝ≥0∞) μ +
        lpNorm (fun ω => b * Y ω) (q : ℝ≥0∞) μ :=
      lpNorm_add_le (memLp_const a) hqone
    _ = a + b * lpNorm Y (q : ℝ≥0∞) μ := by
      rw [lpNorm_const' (by exact_mod_cast hq.ne') (by simp)]
      rw [show (fun ω => b * Y ω) = b • Y by rfl, lpNorm_const_smul]
      simp [Measure.real, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_pos hb]
    _ ≤ a + b * q := by gcongr

end MeasureTheory

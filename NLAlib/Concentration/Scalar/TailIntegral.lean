import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Expectations from tail bounds

Two elementary integral estimates used to turn tail bounds into moment bounds.

* `integrable_and_integral_le_of_tail_le_rpow`: a nonnegative random variable with a
  polynomial tail `P(f > t) ≤ C t^{-m}` (`m > 1`) is integrable with
  `E f ≤ C^{1/m} m / (m - 1)` (layer-cake formula, split at `t = C^{1/m}`).
* `lintegral_rpow_mul_exp_le`: `∫₀ᵗ x^a e^{-x/2} dx ≤ t^{a+1} / (a + 1)` for `a > -1`.

Atlas: `tail-integral`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

/-- **Expectation from a polynomial tail.** If `f ≥ 0` a.e. on a probability space and
`P(f > t) ≤ C t^{-m}` for all `t > 0`, with `C > 0` and `m > 1`, then `f` is integrable and
`E f ≤ C^{1/m} · m / (m - 1)`.

Standard layer-cake estimate (`E f = ∫₀^∞ P(f > t) dt`, bounded by `1` below `C^{1/m}` and by
the tail above), e.g. HMT 2011, proof of Thm 10.8 / Vershynin 2018, Lemma 1.2.1.
Atlas: `tail-integral`. Ported from Prove2me solution
`GaussianMatrix.integral_le_of_tail_bound`.
atlas: tail-integral -/
theorem integrable_and_integral_le_of_tail_le_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * t ^ (-m))) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ C ^ (1 / m) * m / (m - 1) := by
  set a : ℝ := C ^ (1 / m) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hC _
  have hm1 : 0 < m - 1 := by linarith
  -- `C * a ^ (1 - m) = a`
  have hCa : C * a ^ (-m + 1) = a := by
    rw [ha_def, ← Real.rpow_mul hC.le]
    have : 1 / m * (-m + 1) = 1 / m - 1 := by field_simp; ring
    rw [this, Real.rpow_sub_one hC.ne']
    field_simp
  -- the tail integral over `(a, ∞)`
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-m)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul C
  have hval : ∫ t in Ioi a, C * t ^ (-m) = a / (m - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
    have hne : -m + 1 ≠ 0 := by linarith
    have hne' : 1 - m ≠ 0 := by linarith
    rw [show C * (-a ^ (-m + 1) / (-m + 1)) = (C * a ^ (-m + 1)) / (m - 1) by
      field_simp; ring, hCa]
  have hlow : ∫⁻ t in Ioc 0 a, μ {x | t < f x} ≤ ENNReal.ofReal a := by
    calc ∫⁻ t in Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Ioc 0 a, 1 :=
          lintegral_mono fun t => prob_le_one
      _ = ENNReal.ofReal a := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have hhigh : ∫⁻ t in Ioi a, μ {x | t < f x} ≤ ENNReal.ofReal (a / (m - 1)) := by
    calc ∫⁻ t in Ioi a, μ {x | t < f x}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C * t ^ (-m)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => htail t ?_
          exact lt_trans ha ht
      _ = ENNReal.ofReal (∫ t in Ioi a, C * t ^ (-m)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg hC.le (Real.rpow_nonneg (lt_trans ha ht).le _)
      _ = ENNReal.ofReal (a / (m - 1)) := by rw [hval]
  have hbound : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (a * m / (m - 1)) := by
    rw [lintegral_eq_lintegral_meas_lt μ hnn hf, ← Ioc_union_Ioi_eq_Ioi ha.le,
      lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
    calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a / (m - 1)) := add_le_add hlow hhigh
      _ = ENNReal.ofReal (a * m / (m - 1)) := by
          rw [← ENNReal.ofReal_add ha.le (div_nonneg ha.le hm1.le)]
          congr 1
          field_simp
          ring
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (mul_nonneg ha.le (by linarith)) hm1.le) hbound

/-- **Truncated Gamma integral bound.** For `a > -1` and `t ≥ 0`,
`∫₀ᵗ x^a e^{-x/2} dx ≤ t^{a+1} / (a + 1)` (drop the exponential factor).

Elementary; used for the chi-square small-ball density bound (Davidson–Szarek 2001,
Vershynin 2012). Atlas: `tail-integral`. Ported from Prove2me solution
`GaussianMatrix.integral_power_exp_le`.
atlas: tail-integral -/
theorem lintegral_rpow_mul_exp_le {a : ℝ} (ha : -1 < a) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 t) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) ha)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 this
  calc ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        apply ENNReal.ofReal_le_ofReal
        have h1 : 0 ≤ x ^ a := Real.rpow_nonneg hx.1.le _
        have h2 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
        nlinarith
    _ = ENNReal.ofReal (∫ x in Ioc 0 t, x ^ a) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact Real.rpow_nonneg hx.1.le _
    _ = ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
        rw [← intervalIntegral.integral_of_le ht, integral_rpow (Or.inl ha),
          Real.zero_rpow (by linarith), sub_zero]

end NLAlib

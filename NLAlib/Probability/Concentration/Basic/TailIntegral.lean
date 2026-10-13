import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import NLAlib.ForMathlib.Analysis.SpecialFunctions.Gamma

/-!
# Expectations from tail bounds

General tail comparison and two elementary integral estimates used to turn tail bounds
into moment bounds.

* `lintegral_le_of_tail_le`: the nonnegative expectation is at most
  `a + ∫ₐ^∞ F(t) dt`, including an infinite tail integral.
* `integrable_of_tail_le` and `integral_le_of_tail_le`: a nonnegative integrable tail
  envelope proves integrability and bounds the Bochner expectation.
* `integrable_of_tail_le_rpow` and `integral_le_of_tail_le_rpow`: a nonnegative random variable with a
  polynomial tail `P(f > t) ≤ C t^{-m}` (`m > 1`) is integrable with
  `E f ≤ C^{1/m} m / (m - 1)` (layer-cake formula, split at `t = C^{1/m}`).
* `lintegral_rpow_mul_exp_le`: `∫₀ᵗ x^a e^{-x/2} dx ≤ t^{a+1} / (a + 1)` for `a > -1`.

Atlas: `tail-integral`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

/-- **Expectation from a general tail envelope, nonnegative integral form.** If `f ≥ 0`
a.e. on a probability space, `a ≥ 0`, and `P(f > t) ≤ F(t)` for `t > a`, then
`E f ≤ a + ∫ₐ^∞ F(t) dt`. No finiteness or measurability assumption on the envelope
is needed for this extended nonnegative integral inequality.

Standard layer-cake estimate; Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of
Thm 10.8. Uses Mathlib's `lintegral_eq_lintegral_meas_lt`.
atlas: tail-integral -/
theorem lintegral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ)
    (htail : ∀ t : ℝ, a < t → μ.real {x | t < f x} ≤ F t) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal a + ∫⁻ t in Ioi a, ENNReal.ofReal (F t) := by
  rw [lintegral_eq_lintegral_meas_lt μ hnn hf, ← Ioc_union_Ioi_eq_Ioi ha,
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  refine add_le_add ?_ ?_
  · calc ∫⁻ t in Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Ioc 0 a, 1 :=
          lintegral_mono fun _ => prob_le_one
      _ = ENNReal.ofReal a := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | t < f x})]
    exact ENNReal.ofReal_le_ofReal (htail t ht)

/-- **Expectation from a general integrable tail envelope.** A nonnegative random variable
whose upper tail is bounded by a nonnegative integrable `F` above `a ≥ 0` is integrable,
and `E f ≤ a + ∫ₐ^∞ F(t) dt`. Integrability is derived, rather than assumed for `f`.

Standard layer-cake estimate; Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of
Thm 10.8. The nonnegative integral version `lintegral_le_of_tail_le` also covers
infinite tail envelopes.
-/
private theorem integrable_and_integral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi a)) (hFnn : 0 ≤ᵐ[volume.restrict (Ioi a)] F)
    (htail : ∀ t : ℝ, a < t → μ.real {x | t < f x} ≤ F t) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ a + ∫ t in Ioi a, F t := by
  have hbound := lintegral_le_of_tail_le μ f hf hnn ha F htail
  rw [← ofReal_integral_eq_lintegral_ofReal hF hFnn,
    ← ENNReal.ofReal_add ha (integral_nonneg_of_ae hFnn)] at hbound
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg ha (integral_nonneg_of_ae hFnn)) hbound

/-- **Expectation from a polynomial tail.** If `f ≥ 0` a.e. on a probability space and
`P(f > t) ≤ C t^{-m}` for all `t > 0`, with `C > 0` and `m > 1`, then `f` is integrable and
`E f ≤ C^{1/m} · m / (m - 1)`.

Standard layer-cake estimate (`E f = ∫₀^∞ P(f > t) dt`, bounded by `1` below `C^{1/m}` and by
the tail above), e.g. HMT 2011, proof of Thm 10.8 / Vershynin 2018, Lemma 1.2.1.

-/
private theorem integrable_and_integral_le_of_tail_le_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ.real {x | t < f x} ≤ C * t ^ (-m)) :
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
  have hnnF : 0 ≤ᵐ[volume.restrict (Ioi a)] fun t => C * t ^ (-m) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hC.le (Real.rpow_nonneg (lt_trans ha ht).le _)
  obtain ⟨hintf, hle⟩ := integrable_and_integral_le_of_tail_le μ f hf hnn ha.le
    (fun t => C * t ^ (-m)) hint hnnF (fun t ht => htail t (lt_trans ha ht))
  refine ⟨hintf, hle.trans_eq ?_⟩
  rw [hval]
  dsimp only [a]
  field_simp
  ring

/-- Integrability from a nonnegative integrable tail envelope.
Source: Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of Thm 10.8.
atlas: tail-integral -/
theorem integrable_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi a)) (hFnn : 0 ≤ᵐ[volume.restrict (Ioi a)] F)
    (htail : ∀ t : ℝ, a < t → μ.real {x | t < f x} ≤ F t) :
    Integrable f μ :=
  (integrable_and_integral_le_of_tail_le μ f hf hnn ha F hF hFnn htail).1

/-- The expectation bound from a nonnegative integrable tail envelope.
Source: Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of Thm 10.8.
atlas: tail-integral -/
theorem integral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi a)) (hFnn : 0 ≤ᵐ[volume.restrict (Ioi a)] F)
    (htail : ∀ t : ℝ, a < t → μ.real {x | t < f x} ≤ F t) :
    ∫ x, f x ∂μ ≤ a + ∫ t in Ioi a, F t :=
  (integrable_and_integral_le_of_tail_le μ f hf hnn ha F hF hFnn htail).2

/-- Integrability from a polynomial tail envelope.
Source: Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of Thm 10.8.
atlas: tail-integral -/
theorem integrable_of_tail_le_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ.real {x | t < f x} ≤ C * t ^ (-m)) :
    Integrable f μ :=
  (integrable_and_integral_le_of_tail_le_rpow μ f hf hnn C m hC hm htail).1

/-- The expectation bound from a polynomial tail envelope.
Source: Vershynin 2018, Lemma 1.2.1; HMT 2011, proof of Thm 10.8.
atlas: tail-integral -/
theorem integral_le_of_tail_le_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ.real {x | t < f x} ≤ C * t ^ (-m)) :
    ∫ x, f x ∂μ ≤ C ^ (1 / m) * m / (m - 1) :=
  (integrable_and_integral_le_of_tail_le_rpow μ f hf hnn C m hC hm htail).2

end NLAlib

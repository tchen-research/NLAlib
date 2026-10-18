import NLAlib.ForMathlib.MeasureTheory.LogDeficit
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Extended integrals of logarithms

The extended logarithmic integral is the positive-part lintegral minus the
negative-part lintegral. On a finite measure space, an upper bound on the
logarithm makes the first term finite, so the formula has its usual unambiguous
extended-integral meaning. The definitions remain total for arbitrary measures;
no existence of an extended integral is asserted when both parts are infinite.
-/

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- The total extended logarithmic integral, defined from positive and negative
parts using the native extended logarithm. `ENNReal.ofReal` sends nonpositive
real inputs to zero, whose extended logarithm is `-∞`.

This has the usual unambiguous extended-integral interpretation when at least
one part is finite. In particular, a finite measure and an upper logarithmic
bound make the positive part finite. If both parts are infinite, the definition
only follows native total `EReal` subtraction (`∞ - ∞ = -∞`), without asserting
existence of the corresponding mathematical extended integral. -/
def extendedLogIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) : EReal :=
  ((∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) : EReal) -
    ((∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) : EReal)

/-- The exponential of the unnormalized total extended logarithmic integral.
For a probability measure and nonnegative inputs with finite positive
logarithmic part, this is the usual extended geometric mean. For arbitrary
measures the integral is not divided by their mass.

Inputs are clipped by `ENNReal.ofReal`, so nonpositive values count as zero.
A finite positive part and infinite negative part give value zero. If both
parts are infinite, this definition merely inherits the native total `EReal`
subtraction convention; it does not assert existence of a mathematical mean. -/
def geometricMean {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) : ℝ≥0∞ :=
  EReal.exp (extendedLogIntegral μ g)

private theorem deficit_add_posPart (c : ℝ) (hc : 0 ≤ c) (t : EReal) (ht : t ≤ c) :
    ((c : EReal) - t).toENNReal + t.toENNReal =
      ENNReal.ofReal c + (-t).toENNReal := by
  induction t with
  | bot => simp
  | top => exact False.elim (not_le_of_gt (EReal.coe_lt_top c) ht)
  | coe t =>
    have htc : t ≤ c := EReal.coe_le_coe_iff.mp ht
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    rcases le_total 0 t with ht0 | ht0
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ht0), add_zero,
        ← ENNReal.ofReal_add (sub_nonneg.mpr htc) ht0]
      congr 1
      ring
    · rw [ENNReal.ofReal_of_nonpos ht0, add_zero,
        ← ENNReal.ofReal_add hc (neg_nonneg.mpr ht0)]
      simp only [sub_eq_add_neg]

/-- Under an upper logarithmic bound the positive part has finite integral. -/
theorem lintegral_log_posPart_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} {c : ℝ}
    (hle : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ c) :
    (∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) < ∞ := by
  calc
    _ ≤ ∫⁻ _ : α, ENNReal.ofReal c ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hle] with x hx
      simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hx
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

/-- The upper-bound formula agrees with the ordinary positive-minus-negative
extended integral. This also proves that its value does not depend on the bound. -/
theorem upperLogIntegral_eq_extendedLogIntegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ}
    (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ c) :
    upperLogIntegral μ g c = extendedLogIntegral μ g := by
  let p := ∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ
  let q := ∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ
  let d := ∫⁻ x, logDeficit c (g x) ∂μ
  have hp : p ≠ ∞ := ne_of_lt (lintegral_log_posPart_lt_top hle)
  have hm := hg.ennreal_ofReal.ennreal_log
  have hbalance : d + p = ENNReal.ofReal c + q := by
    calc
      _ = ∫⁻ x, logDeficit c (g x) +
          (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ :=
        (lintegral_add_left (hg.logDeficit c) _).symm
      _ = ∫⁻ x, ENNReal.ofReal c +
          (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hle] with x hx using deficit_add_posPart c hc _ hx
      _ = ENNReal.ofReal c + q := by
        rw [lintegral_add_left measurable_const]
        simp [q]
  change (c : EReal) - (d : EReal) = (p : EReal) - (q : EReal)
  by_cases hq : q = ∞
  · have hd : d = ∞ := by
      by_contra hd
      have hsum : d + p = ∞ := by simpa only [hq, add_top] using hbalance
      exact (ENNReal.add_ne_top.mpr ⟨hd, hp⟩) hsum
    simp [hq, hd]
  · have hd : d ≠ ∞ := by
      intro hd
      simp [hd] at hbalance
      exact (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hq⟩) hbalance.symm
    have hreal := congrArg ENNReal.toReal hbalance
    rw [ENNReal.toReal_add hd hp, ENNReal.toReal_add ENNReal.ofReal_ne_top hq,
      ENNReal.toReal_ofReal hc] at hreal
    rw [← EReal.coe_ennreal_toReal hd, ← EReal.coe_ennreal_toReal hp,
      ← EReal.coe_ennreal_toReal hq, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith

/-- Consequently the genuine logarithmic integral has the expected ordinary
integral value whenever the logarithm is integrable and positive arguments hold. -/
theorem extendedLogIntegral_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : 0 ≤ c) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hlog : Integrable (fun x => Real.log (g x)) μ)
    (hle : ∀ᵐ x ∂μ, Real.log (g x) ≤ c) :
    extendedLogIntegral μ g = ((∫ x, Real.log (g x) ∂μ : ℝ) : EReal) := by
  rw [← upperLogIntegral_eq_extendedLogIntegral hg hc ?_]
  · exact upperLogIntegral_eq_integral hpos hlog hle
  · filter_upwards [hpos, hle] with x hx hxle
    simpa only [ENNReal.log_ofReal_of_pos hx, EReal.coe_le_coe_iff] using hxle

/-- The genuine extended logarithmic integral is unaffected by almost-everywhere
changes of its argument. -/
theorem extendedLogIntegral_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ} (hgh : g =ᵐ[μ] h) :
    extendedLogIntegral μ g = extendedLogIntegral μ h := by
  unfold extendedLogIntegral
  congr 1 <;> apply congrArg ENNReal.toEReal <;> apply lintegral_congr_ae
  all_goals filter_upwards [hgh] with x hx; rw [hx]

/-- The genuine extended geometric mean is unaffected by almost-everywhere
changes of its argument. -/
theorem geometricMean_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ} (hgh : g =ᵐ[μ] h) :
    geometricMean μ g = geometricMean μ h :=
  congrArg EReal.exp (extendedLogIntegral_congr_ae hgh)

/-- On a probability space the zero function has logarithmic integral `-∞`. -/
@[simp]
theorem extendedLogIntegral_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    extendedLogIntegral μ (fun _ : α => (0 : ℝ)) = ⊥ := by
  simp [extendedLogIntegral]

/-- On a probability space the geometric mean of zero is zero. -/
@[simp]
theorem geometricMean_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    geometricMean μ (fun _ : α => (0 : ℝ)) = 0 := by
  simp [geometricMean]

/-- The geometric mean is normalized on every nonnegative constant on a
probability space. -/
@[simp]
theorem geometricMean_const {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) :
    geometricMean μ (fun _ : α => a) = ENNReal.ofReal a := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst a
    simp
  · have hlog := extendedLogIntegral_eq_integral (μ := μ)
      (g := fun _ : α => a) measurable_const (c := max (Real.log a) 0)
      (le_max_right _ _) (ae_of_all _ (fun _ => ha0))
      (integrable_const (Real.log a)) (ae_of_all _ (fun _ => le_max_left _ _))
    simpa only [geometricMean, integral_const, probReal_univ, one_smul,
      EReal.exp_coe, Real.exp_log ha0] using congrArg EReal.exp hlog

/-- If the logarithm has finite positive part and infinite negative part, its
genuine extended geometric mean is zero. -/
theorem geometricMean_eq_zero_of_lintegral_negPart_eq_top {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hpos : (∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) ≠ ∞)
    (hneg : (∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) = ∞) :
    geometricMean μ g = 0 := by
  rw [geometricMean, extendedLogIntegral, ← EReal.coe_ennreal_toReal hpos,
    hneg, EReal.coe_ennreal_top,
    EReal.sub_top, EReal.exp_bot]

/-- The upper-bound construction has the same value for any two nonnegative
valid logarithmic upper bounds. -/
theorem upperLogIntegral_eq_of_bounds {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hlec : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ c)
    (hled : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ d) :
    upperLogIntegral μ g c = upperLogIntegral μ g d := by
  rw [upperLogIntegral_eq_extendedLogIntegral hg hc hlec,
    upperLogIntegral_eq_extendedLogIntegral hg hd hled]

end MeasureTheory

import NLAlib.ForMathlib.MeasureTheory.ExtendedLogIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Geometric means with zeros and an infinite negative logarithmic part

For a bounded nonnegative function on a probability space, positive scalar
regularizations converge to the exponential of its genuine extended logarithmic
integral.  The result includes zero functions and nonintegrable negative logarithms.
-/

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- The geometric mean obtained by taking all positive scalar regularizations.
The extended-log identity below supplies its intrinsic interpretation, including zeros. -/
def regularizedGeometricMean {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) : ℝ≥0∞ :=
  ⨅ δ : {δ : ℝ // 0 < δ},
    ENNReal.ofReal (Real.exp (∫ x, Real.log (g x + δ) ∂μ))

/-- A bounded nonnegative function has an integrable logarithm after any positive
scalar regularization. -/
theorem integrable_log_add_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C δ : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) (hδ : 0 < δ) :
    Integrable (fun x => Real.log (g x + δ)) μ := by
  apply (integrable_const (|Real.log δ| + |Real.log (C + δ)|)).mono'
    (hg.add_const δ).log.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  have hl : Real.log δ ≤ Real.log (g x + δ) :=
    Real.log_le_log hδ (le_add_of_nonneg_left (hbound x).1)
  have hu : Real.log (g x + δ) ≤ Real.log (C + δ) :=
    Real.log_le_log (by linarith [(hbound x).1]) (by linarith [(hbound x).2])
  constructor <;> linarith [le_abs_self (Real.log δ), neg_abs_le (Real.log δ),
    le_abs_self (Real.log (C + δ)), abs_nonneg (Real.log (C + δ)), abs_nonneg (Real.log δ)]

/-- The exponentiated regularized logarithmic integral is monotone in the positive
regularization parameter. -/
theorem monotone_exp_integral_log_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Monotone (fun δ : {δ : ℝ // 0 < δ} =>
      ENNReal.ofReal (Real.exp (∫ x, Real.log (g x + δ) ∂μ))) := by
  intro δ η hδη
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply integral_mono (integrable_log_add_of_bounded hg hbound δ.property)
    (integrable_log_add_of_bounded hg hbound η.property)
  intro x
  exact Real.log_le_log (by linarith [(hbound x).1, δ.property]) (by linarith [show (δ : ℝ) ≤ (η : ℝ) from hδη])

/-- Monotone convergence for logarithmic deficits, allowing an infinite limit. -/
theorem tendsto_lintegral_logDeficit_add_inv_nat {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Measurable g) (c : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ x, logDeficit c (g x + 1 / ((n : ℝ) + 1)) ∂μ)
      atTop (𝓝 (∫⁻ x, logDeficit c (g x) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ((hg.add_const _).logDeficit c).aemeasurable
  · filter_upwards [] with x i j hij
    apply logDeficit_antitone c
    apply add_le_add_right
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  · filter_upwards [] with x
    apply (continuous_logDeficit c).continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds (x := g x)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Exponentiating the regularized integrals converges to the actual bounded-above
extended integral.  The upper bound `log (C+1)` controls the regularizations with
parameter at most one. -/
theorem tendsto_exp_integral_log_add_inv_nat {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (∫ x, Real.log (g x + 1 / ((n : ℝ) + 1)) ∂μ)))
      atTop (𝓝 (EReal.exp (upperLogIntegral μ g (Real.log (C + 1))))) := by
  have hdef := tendsto_lintegral_logDeficit_add_inv_nat (μ := μ) hg (Real.log (C + 1))
  have hcoe := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hdef
  have hsub : Tendsto (fun n : ℕ => (Real.log (C + 1) : EReal) -
      ((∫⁻ x, logDeficit (Real.log (C + 1)) (g x + 1 / ((n : ℝ) + 1)) ∂μ) : EReal))
      atTop (𝓝 (upperLogIntegral μ g (Real.log (C + 1)))) := by
    change Tendsto _ atTop (𝓝 ((Real.log (C + 1) : EReal) +
      -((∫⁻ x, logDeficit (Real.log (C + 1)) (g x) ∂μ) : EReal)))
    exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
      (Or.inl (EReal.coe_ne_bot _))).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hcoe.neg)
  have hexp := ENNReal.continuous_exp.continuousAt.tendsto.comp hsub
  apply hexp.congr'
  filter_upwards [] with n
  have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have heq := upperLogIntegral_eq_integral (μ := μ)
    (g := fun x => g x + 1 / ((n : ℝ) + 1))
    (c := Real.log (C + 1))
    (ae_of_all _ (fun x => by linarith [(hbound x).1]))
    (integrable_log_add_of_bounded hg hbound hδ)
    (ae_of_all _ (fun x => Real.log_le_log (by linarith [(hbound x).1])
      (by linarith [(hbound x).2])))
  change EReal.exp (upperLogIntegral μ (fun x => g x + 1 / ((n : ℝ) + 1))
    (Real.log (C + 1))) = _
  rw [heq, EReal.exp_coe]

/-- Positive regularization equals the exponential of the genuine extended
logarithmic integral, including the value zero when the logarithm has infinite
negative part. -/
theorem regularizedGeometricMean_eq_exp_upperLogIntegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    regularizedGeometricMean μ g =
      EReal.exp (upperLogIntegral μ g (Real.log (C + 1))) := by
  have ht := tendsto_exp_integral_log_add_inv_nat (μ := μ) hg hbound
  apply le_antisymm
  · apply ge_of_tendsto' ht
    intro n
    exact iInf_le _ (⟨1 / ((n : ℝ) + 1), by positivity⟩ : {δ : ℝ // 0 < δ})
  · apply le_iInf
    intro δ
    apply le_of_tendsto ht
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_le_const δ.property
    filter_upwards [hsmall] with n hn
    exact monotone_exp_integral_log_add hg hbound
      (show (⟨1 / ((n : ℝ) + 1), by positivity⟩ : {δ : ℝ // 0 < δ}) ≤ δ from hn)

/-- The regularized mean is the genuine extended geometric mean. The logarithmic
integral on the right is defined independently from its positive and negative
parts, with `log 0 = -∞`. No integrability of the negative part is required. -/
theorem regularizedGeometricMean_eq_geometricMean {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    regularizedGeometricMean μ g = geometricMean μ g := by
  rw [regularizedGeometricMean_eq_exp_upperLogIntegral hg hbound, geometricMean,
    upperLogIntegral_eq_extendedLogIntegral hg (Real.log_nonneg (by linarith))]
  filter_upwards [] with x
  by_cases hx : 0 < g x
  · rw [ENNReal.log_ofReal_of_pos hx, EReal.coe_le_coe_iff]
    exact Real.log_le_log hx (by linarith [(hbound x).2])
  · simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hx)]

/-- Any bound valid for every positive regularization passes to the genuine
extended geometric mean, including when it vanishes. -/
theorem le_geometricMean_of_le_exp_integral_log_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C)
    {a : ℝ≥0∞} (ha : ∀ δ : ℝ, 0 < δ →
      a ≤ ENNReal.ofReal (Real.exp (∫ x, Real.log (g x + δ) ∂μ))) :
    a ≤ geometricMean μ g := by
  rw [← regularizedGeometricMean_eq_geometricMean hg hC hbound]
  exact le_iInf (fun δ => ha δ δ.property)

/-- A bounded nonnegative function has a finite extended geometric mean. -/
theorem geometricMean_ne_top_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    geometricMean μ g ≠ ∞ := by
  rw [← regularizedGeometricMean_eq_geometricMean hg hC hbound]
  apply ne_of_lt
  exact lt_of_le_of_lt (iInf_le _ (⟨1, zero_lt_one⟩ : {δ : ℝ // 0 < δ}))
    ENNReal.ofReal_lt_top

end MeasureTheory

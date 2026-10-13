import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating finite conditional event estimates

The independent product law splits into the first-coordinate bad
event and the bound for every remaining section. Supports `srht-ose`.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace MeasureTheory

/-- A finite product event's real probability is the integral of its
section probabilities. Source: finite Fubini; supports `srht-ose`. -/
theorem measureReal_prod_eq_integral_sections
    {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Set (α × β)) :
    (μ.prod ν).real F = ∫ x, ν.real {y | (x, y) ∈ F} ∂μ := by
  simp only [measureReal_def]
  rw [Measure.prod_apply (MeasurableSet.of_discrete)]
  symm
  exact integral_toReal Measurable.of_discrete.aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))

/-- Integrating a conditional bound outside a first-coordinate bad
event gives the sum of that event probability and the conditional bound.
Source: `srht-ose` final conditioning step. -/
theorem measureReal_prod_le_measureReal_add_of_sections_le
    {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set α) (F : Set (α × β)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, x ∉ E → ν.real {y | (x, y) ∈ F} ≤ c) :
    (μ.prod ν).real F ≤ μ.real E + c := by
  rw [measureReal_prod_eq_integral_sections]
  calc
    _ ≤ ∫ x, E.indicator (fun _ => (1 : ℝ)) x + c ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x
      dsimp only
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        exact (measureReal_le_one (μ := ν)).trans (by linarith)
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact hF x hx
    _ = _ := by
      have hi : (∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real E := by
        simpa only [smul_eq_mul, mul_one, measureReal_def] using
          integral_indicator_const (μ := μ) (1 : ℝ) (show MeasurableSet E from .of_discrete)
      rw [integral_add Integrable.of_finite Integrable.of_finite, hi]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- A measurable product event's real probability is the integral of its section
probabilities, for arbitrary probability spaces. -/
theorem measureReal_prod_eq_integral_sections_of_measurableSet
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Set (α × β)) (hF : MeasurableSet F) :
    (μ.prod ν).real F = ∫ x, ν.real {y | (x, y) ∈ F} ∂μ := by
  simp only [measureReal_def]
  rw [Measure.prod_apply hF]
  symm
  exact integral_toReal (measurable_measure_prodMk_left hF).aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))

/-- Integrate an almost-everywhere conditional event bound outside a measurable
first-coordinate bad event, on arbitrary probability spaces. -/
theorem measureReal_prod_le_measureReal_add_of_sections_le_of_measurableSet
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set α) (F : Set (α × β)) (hE : MeasurableSet E) (hFm : MeasurableSet F)
    {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ᵐ x ∂μ, x ∉ E → ν.real {y | (x, y) ∈ F} ≤ c) :
    (μ.prod ν).real F ≤ μ.real E + c := by
  have hsec : Integrable (fun x => ν.real {y | (x, y) ∈ F}) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_measure_prodMk_left hFm).ennreal_toReal.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  rw [measureReal_prod_eq_integral_sections_of_measurableSet μ ν F hFm]
  calc
    _ ≤ ∫ x, E.indicator (fun _ => (1 : ℝ)) x + c ∂μ := by
      apply integral_mono_ae hsec (hi.add (integrable_const c))
      filter_upwards [hF] with x hxF
      change ν.real {y | (x, y) ∈ F} ≤ E.indicator (fun _ => (1 : ℝ)) x + c
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        exact (measureReal_le_one (μ := ν)).trans (by linarith)
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact hxF hx
    _ = _ := by
      have hi' : (∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real E := by
        simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) hE
      rw [integral_add hi (integrable_const c), hi']
      simp only [integral_const, probReal_univ, one_smul]

end MeasureTheory

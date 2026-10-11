import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Integrating finite conditional event estimates

The actual independent product law splits into the first-coordinate bad
event and the bound for every remaining section. Supports `sh:srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical
namespace NLAlib

/-- A finite product event's real probability is the integral of its actual
section probabilities. Source: finite Fubini; supports `srht-ose`. -/
theorem measureReal_prod_eq_integral_sections
    {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Set (α × β)) :
    ((μ.prod ν) F).toReal = ∫ x, (ν {y | (x, y) ∈ F}).toReal ∂μ := by
  rw [Measure.prod_apply (MeasurableSet.of_discrete)]
  symm
  exact integral_toReal Measurable.of_discrete.aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))

/-- Integrating a genuine conditional bound outside a first-coordinate bad
event gives the sum of that event probability and the conditional bound.
Source: `sh:srht-ose` final conditioning step. -/
theorem measureReal_prod_le_bad_add
    {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set α) (F : Set (α × β)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, x ∉ E → (ν {y | (x, y) ∈ F}).toReal ≤ c) :
    ((μ.prod ν) F).toReal ≤ (μ E).toReal + c := by
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
      have hi : (∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂μ) = (μ E).toReal := by
        simpa only [smul_eq_mul, mul_one, measureReal_def] using
          integral_indicator_const (μ := μ) (1 : ℝ) (show MeasurableSet E from .of_discrete)
      rw [integral_add Integrable.of_finite Integrable.of_finite, hi]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

end NLAlib

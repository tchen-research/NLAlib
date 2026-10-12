import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of one-coordinate conditional means

`measurable_integral_update_pi`: `x ↦ ∫ f (update x i t) dμᵢ(t)` is measurable. Next to
`integrable_integral_update_pi` (`NLAlib.ForMathlib.MeasureTheory.Integral`). Moved from
`NLAlib.Probability.Concentration.Entropy.EntropyTensorizationNonneg` (dedup round, 2026-10-12).
-/

open MeasureTheory

namespace NLAlib

/-- A one-coordinate conditional mean is measurable. Source: Mathlib's
`StronglyMeasurable.integral_prod_right'` applied to coordinate resampling.
Atlas: `entropy-tensorization`. -/
theorem measurable_integral_update_pi {ι : Type*} [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) {f : (ι → Ω) → ℝ}
    (hfm : Measurable f) :
    Measurable (fun x => ∫ t, f (Function.update x i t) ∂(μ i)) := by
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : (ι → Ω) × Ω => f (Function.update p.1 i p.2))
    (hfm.comp measurable_update').stronglyMeasurable).measurable

end NLAlib

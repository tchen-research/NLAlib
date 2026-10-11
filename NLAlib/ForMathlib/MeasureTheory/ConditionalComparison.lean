import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditional comparison on measurable cuts

The actual pull-out property of indicators preserves an integrable scalar comparison
on any event measurable with respect to the conditioning sigma-algebra.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NLAlib

/-- An integrable real comparison on a conditioning-measurable cut remains true for
the actual conditional expectations on that cut.
Source: Mathlib conditional indicator pull-out and conditional monotonicity;
helper for operator rederivations `eq:condlieb`, atlas `matrix-freedman` (partial). -/
theorem ae_condExp_le_condExp_on_of_ae_le_on {Ω : Type*}
    {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    {s : Set Ω} (hs : MeasurableSet[m] s) (hXY : ∀ᵐ ω ∂μ, ω ∈ s → X ω ≤ Y ω) :
    ∀ᵐ ω ∂μ, ω ∈ s → μ[X | m] ω ≤ μ[Y | m] ω := by
  have hpoint : s.indicator X ≤ᵐ[μ] s.indicator Y := by
    filter_upwards [hXY] with ω hω
    by_cases hsω : ω ∈ s
    · simpa only [Set.indicator_of_mem hsω] using hω hsω
    · simp only [Set.indicator_of_notMem hsω, le_refl]
  have h := condExp_mono (m := m) (hX.indicator (hm _ hs)) (hY.indicator (hm _ hs)) hpoint
  filter_upwards [h, condExp_indicator hX hs, condExp_indicator hY hs] with ω hω h₁ h₂
  intro hsω
  rw [h₁, h₂] at hω
  simpa only [Set.indicator_of_mem hsω] using hω

end NLAlib

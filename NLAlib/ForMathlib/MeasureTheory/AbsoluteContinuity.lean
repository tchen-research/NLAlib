import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Absolute continuity depends only on interval values

Transport the existing Mathlib property across equality on its interval.
Helper for `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Set Filter

namespace NLAlib

/-- Equality on an interval transports absolute continuity, in any metric codomain.
Source: the finite disjoint-interval definition; helper for the AC primitive in
`chebyshev-coeff-bv-decay`. -/
theorem absolutelyContinuousOnInterval_congr {X : Type*} [PseudoMetricSpace X]
    {f g : ℝ → X} {a b : ℝ} (heq : EqOn f g (uIcc a b))
    (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInterval g a b := by
  apply hf.congr'
  have hd : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    (Filter.eventually_principal.mpr fun E hE => hE).filter_mono inf_le_right
  filter_upwards [hd] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq (hE.1 i hi).1, heq (hE.1 i hi).2]

end NLAlib

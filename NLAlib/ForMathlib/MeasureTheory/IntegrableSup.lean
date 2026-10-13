import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Integrability of finite maxima and minima

The pointwise maximum and minimum of finitely many (nonempty index) measurable integrable real
functions are integrable (`integrable_iSup_of_fintype`, `integrable_iInf_of_fintype`): both are
dominated by `∑ₜ |fₜ|`. `exact?` finds no Mathlib lemma of this shape. Used by Gordon's
inequality (atlas `gordon`).
-/

open MeasureTheory

namespace MeasureTheory

/-- The pointwise maximum of finitely many (nonempty index) measurable integrable functions is
integrable.gordon_upper` (helper
`gu_integrable_iSup`). Atlas: helper of `gordon`. -/
theorem integrable_iSup_of_fintype {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨆ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iSup hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddAbove (Set.range fun t => f t ω) := (Set.finite_range _).bddAbove
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · have h1 := le_ciSup hb t0
    have h2 := hs t0
    have := neg_abs_le (f t0 ω)
    linarith
  · exact ciSup_le fun t => (le_abs_self _).trans (hs t)

/-- The pointwise minimum of finitely many (nonempty index) measurable integrable functions is
integrable.gordon_lower` (helper
`gl_integrable_iInf`). Atlas: helper of `gordon`. -/
theorem integrable_iInf_of_fintype {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨅ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iInf hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddBelow (Set.range fun t => f t ω) := (Set.finite_range _).bddBelow
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · refine le_ciInf fun t => ?_
    have := neg_abs_le (f t ω)
    have := hs t
    linarith
  · have h1 := ciInf_le hb t0
    have h2 := hs t0
    have := le_abs_self (f t0 ω)
    linarith

end MeasureTheory

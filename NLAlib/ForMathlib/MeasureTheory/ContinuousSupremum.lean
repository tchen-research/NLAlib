import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Measurable and integrable suprema of continuous real tests

A bounded-above supremum of continuous tests is measurable even for an
uncountable parameter class. A uniform absolute bound then supplies Bochner
integrability on every finite measure space.
-/

noncomputable section
set_option autoImplicit false

namespace Real

/-- A common absolute bound controls the absolute value of the supremum
over any nonempty real parameter class. -/
theorem abs_ciSup_le_of_abs_le {T : Type*} [Nonempty T]
    (f : T → ℝ) {M : ℝ} (h : ∀ t, |f t| ≤ M) : |⨆ t, f t| ≤ M := by
  have hb : BddAbove (Set.range f) := ⟨M, by
    rintro _ ⟨t, rfl⟩
    exact (le_abs_self _).trans (h t)⟩
  rw [abs_le]
  constructor
  · let t : T := Classical.choice inferInstance
    exact (abs_le.mp (h t)).1.trans (le_ciSup hb t)
  · exact ciSup_le fun t => (le_abs_self _).trans (h t)

end Real

namespace MeasureTheory

/-- The supremum of continuous real tests is measurable when its range is
bounded above at every sample. The parameter class can be uncountable. -/
theorem measurable_ciSup_of_continuous_of_bddAbove
    {T E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (f : E → T → ℝ)
    (hf : ∀ t, Continuous (fun x => f x t))
    (hb : ∀ x, BddAbove (Set.range (f x))) :
    Measurable (fun x => ⨆ t, f x t) :=
  (lowerSemicontinuous_ciSup hb (fun t => (hf t).lowerSemicontinuous)).measurable

/-- Uniformly absolutely bounded continuous tests have an integrable
supremum under every finite measure, with no countability assumption on
the nonempty parameter class. -/
theorem integrable_ciSup_of_continuous_of_abs_le
    {T E : Type*} [Nonempty T] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → T → ℝ) (hf : ∀ t, Continuous (fun x => f x t))
    {M : ℝ} (h : ∀ x t, |f x t| ≤ M) :
    Integrable (fun x => ⨆ t, f x t) μ := by
  have hm := measurable_ciSup_of_continuous_of_bddAbove f hf (fun x =>
    ⟨M, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (h x t)⟩)
  apply Integrable.of_bound hm.aestronglyMeasurable M
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_ciSup_le_of_abs_le (f x) (h x)

end MeasureTheory

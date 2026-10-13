import NLAlib.Sketching.Sparse.FiniteLaw.LocalMoments
import NLAlib.Sketching.Sparse.FiniteLaw.ToMeasure

/-!
# Native marginal laws for limited independence

The observable-based finite proof interface `MatchesUpTo` is equivalent to equality of the
ordinary restricted-coordinate laws. Users can establish marginal laws using Mathlib and use
this bridge to enter the sparse moment argument. The finite-sum backend is not a second
definition of limited independence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLAlib.SparseSketch.FiniteLaw

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Equality of all restricted-coordinate laws up to size `k` suffices for the local-observable
interface. The two full laws may have completely different higher-order dependencies. -/
theorem matchesUpTo_of_map_restrict_eq {μ ν : FiniteLaw (ι → α)} {k : ℕ}
    (h : ∀ S : Finset ι, S.card ≤ k →
      μ.toMeasure.map (fun x : ι → α => fun i : S => x i) =
        ν.toMeasure.map (fun x : ι → α => fun i : S => x i)) :
    MatchesUpTo μ ν k := by
  classical
  intro S hS f hf
  let x₀ : ι → α := μ.toPMF.support_nonempty.choose
  let r : (ι → α) → (S → α) := fun x i => x i
  let g : (S → α) → ℝ := fun y => f (fun i => if hi : i ∈ S then y ⟨i, hi⟩ else x₀ i)
  have hfg : f = g ∘ r := by
    funext x
    apply hf
    intro i hi
    simp [r, hi]
  have hm : HasLaw r (μ.toMeasure.map r) μ.toMeasure :=
    ⟨(measurable_of_finite r).aemeasurable, rfl⟩
  have hn : HasLaw r (ν.toMeasure.map r) ν.toMeasure :=
    ⟨(measurable_of_finite r).aemeasurable, rfl⟩
  rw [← integral_toMeasure, ← integral_toMeasure, hfg,
    hm.integral_comp (measurable_of_finite g).aestronglyMeasurable,
    hn.integral_comp (measurable_of_finite g).aestronglyMeasurable]
  rw [h S hS]

/-- Matching every local observable is exactly equality of the native marginal measures. -/
theorem matchesUpTo_iff_map_restrict_eq {μ ν : FiniteLaw (ι → α)} {k : ℕ} :
    MatchesUpTo μ ν k ↔ ∀ S : Finset ι, S.card ≤ k →
      μ.toMeasure.map (fun x : ι → α => fun i : S => x i) =
        ν.toMeasure.map (fun x : ι → α => fun i : S => x i) := by
  classical
  constructor
  · intro h S hS
    let r : (ι → α) → (S → α) := fun x i => x i
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (measurable_of_finite r) hs,
      Measure.map_apply (measurable_of_finite r) hs]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change μ.toMeasure.real (r ⁻¹' s) = ν.toMeasure.real (r ⁻¹' s)
    rw [real_toMeasure, real_toMeasure]
    apply h S hS
    intro x y hxy
    have hr : r x = r y := by
      funext i
      exact hxy i i.property
    change (if r x ∈ s then (1 : ℝ) else 0) = if r y ∈ s then 1 else 0
    rw [hr]
  · exact matchesUpTo_of_map_restrict_eq

end NLAlib.SparseSketch.FiniteLaw

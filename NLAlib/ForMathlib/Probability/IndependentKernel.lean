import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional integration of an independent kernel

Independence identifies the joint law with a product. Applying Fubini also on
events determined by the first coordinate identifies the conditional expectation.
This does not require a regular conditional distribution or a standard Borel space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure β} [IsProbabilityMeasure ν]

/-- A uniform measurable-event bound under the second marginal remains valid
when the first parameter is randomized independently. -/
theorem IndepFun.measure_mem_le_of_forall
    {X : Ω → α} {Y : Ω → β} (hind : IndepFun X Y μ)
    (hX : AEMeasurable X μ) (hY : HasLaw Y ν μ)
    {s : Set (α × β)} (hs : MeasurableSet s) {c : ENNReal}
    (hbound : ∀ x, ν {y | (x, y) ∈ s} ≤ c) :
    μ {ω | (X ω, Y ω) ∈ s} ≤ c := by
  have hXL : HasLaw X (μ.map X) μ := ⟨hX, rfl⟩
  have hXY := hind.hasLaw_prod hXL hY
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  calc
    μ {ω | (X ω, Y ω) ∈ s} = ((μ.map X).prod ν) s := hXY.measure_eq hs
    _ = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ.map X := Measure.prod_apply hs
    _ ≤ ∫⁻ _x, c ∂μ.map X := lintegral_mono hbound
    _ = c := by simp

/-- An integrable independent kernel whose inner mean is a constant has that
conditional mean given its first coordinate. Equality of the inner mean is only
required almost everywhere under the law of that coordinate. -/
theorem IndepFun.condExp_comp_eq_const
    {X : Ω → α} {Y : Ω → β} (hind : IndepFun X Y μ)
    (hX : Measurable X) (hY : HasLaw Y ν μ) {f : α × β → ℝ}
    (hf : Integrable f ((μ.map X).prod ν)) {c : ℝ}
    (hmean : ∀ᵐ x ∂μ.map X, ∫ y, f (x, y) ∂ν = c) :
    μ[fun ω => f (X ω, Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun _ => c := by
  have hXL : HasLaw X (μ.map X) μ := ⟨hX.aemeasurable, rfl⟩
  have hXY := hind.hasLaw_prod hXL hY
  have hfi : Integrable (fun ω => f (X ω, Y ω)) μ := by
    have hf' : Integrable f (μ.map fun ω => (X ω, Y ω)) := by rwa [hXY.map_eq]
    exact hf'.comp_aemeasurable hXY.aemeasurable
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hfi
    (fun s _ _ => (integrable_const c).integrableOn) ?_
    aestronglyMeasurable_const).symm
  rintro s ⟨t, ht, rfl⟩ _
  let u : Set (α × β) := Prod.fst ⁻¹' t
  have hu : MeasurableSet u := ht.preimage measurable_fst
  have hIf := hf.indicator hu
  have hIc : Integrable (u.indicator (fun _ : α × β => c)) ((μ.map X).prod ν) :=
    (integrable_const c).indicator hu
  have hleft := hXY.integral_comp hIc.aestronglyMeasurable
  have hright := hXY.integral_comp hIf.aestronglyMeasurable
  rw [← integral_indicator (ht.preimage hX), ← integral_indicator (ht.preimage hX)]
  change (∫ ω, (u.indicator (fun _ : α × β => c)) (X ω, Y ω) ∂μ) =
    ∫ ω, (u.indicator f) (X ω, Y ω) ∂μ
  rw [show (∫ ω, (u.indicator (fun _ : α × β => c)) (X ω, Y ω) ∂μ) =
    ∫ p, (u.indicator (fun _ : α × β => c)) p ∂((μ.map X).prod ν) from hleft,
    show (∫ ω, (u.indicator f) (X ω, Y ω) ∂μ) =
    ∫ p, (u.indicator f) p ∂((μ.map X).prod ν) from hright,
    integral_prod _ hIc, integral_prod _ hIf]
  apply integral_congr_ae
  filter_upwards [hmean] with x hx
  by_cases hxt : x ∈ t
  · simpa [u, hxt] using hx.symm
  · simp [u, hxt]

end ProbabilityTheory

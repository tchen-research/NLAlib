import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independence after mixing independent sections with a common marginal

Conditional on a separate index, two variables may have different first
marginals. Independence survives mixing when the second marginal is fixed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace ProbabilityTheory

variable {I Ω A B : Type*} [MeasurableSpace I] [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]

/-- Sectionwise common laws give a common law after adjoining an independent
index. This uses the actual product measure, rather than conditional laws. -/
theorem hasLaw_prod_of_sections
    {ρ : Measure I} {ν : Measure Ω} {γ : Measure B}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {g : I × Ω → B} (hg : Measurable g)
    (hγ : ∀ i, HasLaw (fun ω => g (i, ω)) γ ν) : HasLaw g γ (ρ.prod ν) := by
  refine ⟨hg.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hg ht, Measure.prod_apply (hg ht)]
  have he (i : I) : ν ((Prod.mk i) ⁻¹' (g ⁻¹' t)) = γ t := by
    exact (hγ i).measurePreserving (hg.comp measurable_prodMk_left) |>.measure_preimage ht.nullMeasurableSet
  simp_rw [he]
  simp

/-- With a countable separately sampled index, section laws mix by the actual
measure bind. The section distributions are allowed to vary with the index. -/
theorem hasLaw_prod_of_section_laws [Countable I] [MeasurableSingletonClass I]
    {ρ : Measure I} {ν : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {γ : I → Measure B} {g : I × Ω → B} (hg : Measurable g)
    (hγ : ∀ i, HasLaw (fun ω => g (i, ω)) (γ i) ν) :
    HasLaw g (ρ.bind γ) (ρ.prod ν) := by
  refine ⟨hg.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hg ht, Measure.prod_apply (hg ht),
    Measure.bind_apply ht (measurable_of_countable γ).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [] with i
  exact (hγ i).measurePreserving (hg.comp measurable_prodMk_left) |>.measure_preimage ht.nullMeasurableSet

/-- If sections are independent and the second marginal law is constant, then
mixing with an independent index preserves independence. The first marginal
law may depend on the index. -/
theorem indepFun_prod_of_sections
    {ρ : Measure I} {ν : Measure Ω} {γ : Measure B}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {f : I × Ω → A} {g : I × Ω → B} (hf : Measurable f) (hg : Measurable g)
    (hind : ∀ i, IndepFun (fun ω => f (i, ω)) (fun ω => g (i, ω)) ν)
    (hγ : ∀ i, HasLaw (fun ω => g (i, ω)) γ ν) : IndepFun f g (ρ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmass (i : I) : ν ((Prod.mk i) ⁻¹' (g ⁻¹' t)) = γ t := by
    exact (hγ i).measurePreserving (hg.comp measurable_prodMk_left) |>.measure_preimage ht.nullMeasurableSet
  have hprod (i : I) : ν ((Prod.mk i) ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t)) =
      ν ((Prod.mk i) ⁻¹' (f ⁻¹' s)) * γ t := by
    change ν ((fun ω => f (i, ω)) ⁻¹' s ∩ (fun ω => g (i, ω)) ⁻¹' t) = _
    rw [(hind i).measure_inter_preimage_eq_mul s t hs ht]
    have hm := hmass i
    change ν ((fun ω => g (i, ω)) ⁻¹' t) = γ t at hm
    rw [hm]
    rfl
  have hmap := (hasLaw_prod_of_sections (ρ := ρ) hg hγ).map_eq
  have hgt : (ρ.prod ν) (g ⁻¹' t) = γ t := by
    rw [← Measure.map_apply hg ht, hmap]
  rw [Measure.prod_apply ((hf hs).inter (hg ht)), hgt,
    Measure.prod_apply (hf hs)]
  simp_rw [hprod]
  exact lintegral_mul_const' _ _ (measure_ne_top γ t)

end ProbabilityTheory

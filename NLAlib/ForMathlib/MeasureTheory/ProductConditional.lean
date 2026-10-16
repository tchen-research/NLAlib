import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation on the first coordinate of a product

An explicitly evaluated inner integral is the conditional expectation on the
first factor. This elementary Fubini form avoids conditional probability kernels.
-/

noncomputable section
open MeasureTheory
namespace MeasureTheory

variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If the inner integral of a product-integrable function equals a strongly
measurable function `g`, then `g ∘ Prod.fst` is its conditional expectation on
the first coordinate. -/
theorem condExp_prod_fst_of_integral_eq
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A × B → E} {g : A → E} (hf : Integrable f (μ.prod ν))
    (hg : StronglyMeasurable g) (he : ∀ x, ∫ y, f (x, y) ∂ν = g x) :
    (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod ν]
      fun p => g p.1 := by
  have hgi : Integrable g μ := by simpa only [he] using hf.integral_prod_left
  have hgp : Integrable (fun p : A × B => g p.1) (μ.prod ν) := hgi.comp_fst ν
  have hfst : @Measurable (A × B) A
      (MeasurableSpace.comap Prod.fst inferInstance) _ Prod.fst :=
    measurable_iff_comap_le.mpr le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun s _ _ => hgp.integrableOn) ?_ (hg.comp_measurable hfst).aestronglyMeasurable).symm
  rintro s ⟨t, ht, rfl⟩ hs
  have hset : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set B) := by ext p; simp
  rw [hset, setIntegral_prod _ hgp.integrableOn, setIntegral_prod _ hf.integrableOn]
  simp only [integral_const, Measure.restrict_univ, probReal_univ, one_smul, he]

end MeasureTheory

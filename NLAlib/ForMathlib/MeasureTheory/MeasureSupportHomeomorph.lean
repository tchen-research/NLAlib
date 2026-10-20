import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Map

/-! # Exact measure supports under homeomorphisms

A genuine homeomorphism preserves positive neighborhoods and maps the
closed conull support to a closed conull set. This gives the exact
support identity without compactness or an assumed support formula.
-/

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace MeasureTheory.Measure
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [HereditarilyLindelofSpace X]

/-- The actual support of a push-forward under a homeomorphism is
exactly the image of the original support. Compactness and finite
mass are unnecessary. -/
theorem support_map_homeomorph (ν : Measure X) (e : X ≃ₜ Y) :
    (ν.map e).support=e '' ν.support := by
  have hc : IsClosed (e '' ν.support) := e.isClosedMap _ ν.isClosed_support
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed hc
    apply (ae_map_iff e.continuous.measurable.aemeasurable hc.measurableSet).mpr
    have hs : ∀ᵐ x ∂ν,x∈ν.support := ν.support_mem_ae
    exact hs.mono fun x hx => ⟨x,hx,rfl⟩
  · rintro y ⟨x,hx,rfl⟩
    apply (mem_support_iff_forall _).mpr
    intro U hU
    have hp := (mem_support_iff_forall x).mp hx (e ⁻¹' U)
      (e.continuous.continuousAt.preimage_mem_nhds hU)
    exact hp.trans_le (le_map_apply e.continuous.measurable.aemeasurable U)

end MeasureTheory.Measure

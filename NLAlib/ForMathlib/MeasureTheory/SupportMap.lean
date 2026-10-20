import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Compactness.Compact

/-!
# Support of a continuous image of a compact fully supported measure

Every point in the range remains in support by continuity and the source's
actual support property. Compactness makes the range closed and gives the
reverse inclusion, including empty compact domains and zero measures.
-/

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace MeasureTheory.Measure
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [T2Space Y]

/-- The image of a compact fully supported measure under a continuous map has support exactly the range of the map. -/
theorem support_map_eq_range_of_compact (μ : Measure X) (f : X → Y)
    (hf : Continuous f) (hfull : μ.support=Set.univ) :
    (μ.map f).support=Set.range f := by
  have hr : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed hr
    apply (ae_map_iff hf.measurable.aemeasurable hr.measurableSet).mpr
    exact Filter.Eventually.of_forall fun x => ⟨x,rfl⟩
  · rintro y ⟨x,rfl⟩
    apply (mem_support_iff_forall _).mpr
    intro U hU
    have hx : x∈μ.support := by rw [hfull]; trivial
    have hp := (mem_support_iff_forall x).mp hx (f ⁻¹' U) (hf.continuousAt.preimage_mem_nhds hU)
    exact hp.trans_le (le_map_apply hf.measurable.aemeasurable U)

end MeasureTheory.Measure

import NLAlib.ForMathlib.Topology.CubicalMaps
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Active-edge properties under continuous chain maps

Native supported submodules transport arbitrary active-edge properties.
Injective continuous maps also reflect active edges, so geometric subtype
lifts preserve regularity without introducing any new parameterization.
-/

noncomputable section
open scoped unitInterval
namespace Cubical
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The image of an actual active edge under an injective continuous map
is active, and no cancellation can hide such an edge. -/
theorem mem_support_mapOne_comp_iff (f : C(X, Y)) (hf : Function.Injective f)
    (Γ : OneChain X) (γ : C(I, X)) :
    f.comp γ ∈ (mapOne f Γ).support ↔ γ ∈ Γ.support := by
  simp only [Finsupp.mem_support_iff]
  change Finsupp.mapDomain (fun δ : C(I, X) => f.comp δ) Γ (f.comp γ) ≠ 0 ↔ Γ γ ≠ 0
  rw [Finsupp.mapDomain_apply (comp_injective f hf)]

/-- A continuous chain image transports every actual active-edge property
that holds on all the images of the original active edges. -/
theorem mapOne_mem_supported (f : C(X, Y)) (Γ : OneChain X) (S : Set C(I, Y))
    (hΓ : ∀ γ ∈ Γ.support, f.comp γ ∈ S) :
    mapOne f Γ ∈ Finsupp.supported ℤ ℤ S := by
  exact Finsupp.supported_comap_lmapDomain ℤ ℤ (fun γ : C(I, X) => f.comp γ) S hΓ

end Cubical

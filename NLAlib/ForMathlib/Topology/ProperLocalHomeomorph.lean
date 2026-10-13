import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper local homeomorphisms over simply connected spaces

Mathlib's finite-fiber covering theorem and lift uniqueness give the global
inverse needed for the peak-difference map in `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Function Topology

namespace NLAlib

/-- A proper local homeomorphism between Hausdorff spaces is a covering map.
Source: compact discrete fibers and Mathlib's closed-map covering theorem;
helper for `lebesgue-constant-lower-bound`. -/
theorem isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E] [T2Space X]
    {f : E → X} (hf : IsProperMap f) (hlocal : IsLocalHomeomorph f) : IsCoveringMap f := by
  have hfinite (x : X) : (f ⁻¹' {x}).Finite := by
    have himage : (f '' (f ⁻¹' {x})).Finite :=
      (finite_singleton x).subset (by rintro _ ⟨e, he, rfl⟩; exact he)
    exact (hf.isCompact_preimage isCompact_singleton).finite
      (hlocal.isLocalHomeomorphOn.isDiscrete_of_image himage.isDiscrete)
  intro x
  exact hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph (hfinite x)
    (fun e _ => by
      obtain ⟨φ, he, hφ⟩ := hlocal e
      exact ⟨φ, he, hφ.symm⟩)

/-- A proper local homeomorphism with connected nonempty domain and simply connected
locally path-connected target is bijective.
Source: unique lifting of the identity followed by uniqueness of connected lifts;
helper for `lebesgue-constant-lower-bound`. -/
theorem bijective_of_isProperMap_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E] [T2Space X]
    [Nonempty E] [PreconnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : E → X} (hf : IsProperMap f) (hlocal : IsLocalHomeomorph f) : Bijective f := by
  have hcov := isCoveringMap_of_isProperMap_of_isLocalHomeomorph hf hlocal
  let e : E := Classical.arbitrary E
  obtain ⟨g, hg, _⟩ := hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e) e rfl
  have hgf : (g : X → E) ∘ f = id := by
    apply hcov.eq_of_comp_eq (g.continuous.comp hf.continuous) continuous_id
    · ext x
      exact congrFun hg.2 (f x)
    · exact hg.1
  constructor
  · intro x y hxy
    have h := congrArg g hxy
    exact (congrFun hgf x).symm.trans (h.trans (congrFun hgf y))
  · intro x
    exact ⟨g x, congrFun hg.2 x⟩

end NLAlib

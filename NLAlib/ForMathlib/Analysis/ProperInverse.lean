import NLAlib.ForMathlib.Topology.ProperLocalHomeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Global smooth inverses on open connected domains

An everywhere invertible strict derivative and properness of the restricted map
give a global inverse with its actual derivative. Helper for the peak comparison
in `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Filter Function Topology

namespace NLAlib

/-- An open-domain map with invertible strict derivative and proper restriction
has a global inverse with inverse derivative.
Source: the inverse function theorem and proper covering-map uniqueness;
helper for `lebesgue-constant-lower-bound`. -/
theorem exists_inverse_of_isProperMap_of_hasStrictFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} [Nonempty U] [PreconnectedSpace U] (hU : IsOpen U)
    {f : E → E} {D : E → E ≃L[ℝ] E}
    (hf : ∀ x ∈ U, HasStrictFDerivAt f (D x : E →L[ℝ] E) x)
    (hproper : IsProperMap (fun x : U => f x)) :
    ∃ g : E → E, Continuous g ∧ (∀ y, g y ∈ U) ∧
      (∀ y, f (g y) = y) ∧ (∀ x ∈ U, g (f x) = x) ∧
      ∀ y, HasStrictFDerivAt g ((D (g y)).symm : E →L[ℝ] E) y := by
  have hOn : IsLocalHomeomorphOn f U := by
    intro x hx
    exact ⟨(hf x hx).toOpenPartialHomeomorph f,
      (hf x hx).mem_toOpenPartialHomeomorph_source,
      (hf x hx).toOpenPartialHomeomorph_coe.symm⟩
  have hlocal : IsLocalHomeomorph (fun x : U => f x) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hOn.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (fun x _ => x.property)
  have hb := bijective_of_isProperMap_of_isLocalHomeomorph hproper hlocal
  let e : U ≃ₜ E := hlocal.toHomeomorphOfBijective hb
  let g : E → E := fun y => (e.symm y : E)
  have hgU (y : E) : g y ∈ U := (e.symm y).property
  have hright (y : E) : f (g y) = y := e.apply_symm_apply y
  have hleft (x : E) (hx : x ∈ U) : g (f x) = x := by
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  refine ⟨g, continuous_subtype_val.comp e.symm.continuous, hgU, hright, hleft, ?_⟩
  intro y
  have hevent : ∀ᶠ x in 𝓝 (g y), g (f x) = x := by
    filter_upwards [hU.mem_nhds (hgU y)] with x hx
    exact hleft x hx
  have hd := (hf (g y) (hgU y)).to_local_left_inverse hevent
  rwa [hright y] at hd

end NLAlib

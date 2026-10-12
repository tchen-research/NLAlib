import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# Neighborhood continuity of an implicit function

The inverse supplied by the implicit function theorem is continuous on its
open target. In particular its product-domain branch is continuous at every
point of a neighborhood of the base parameter.
-/

noncomputable section
open Filter
open scoped Topology

namespace NLAlib

/-- The product-domain implicit function is continuous throughout a
neighborhood of the base parameter. This is the open partial homeomorphism
conclusion of the implicit function theorem; helper for
`simple-eigenvalue-perturbation`. -/
theorem eventually_continuousAt_implicitFunctionOfProdDomain
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {f : E × F → G} {D : (E × F) →L[𝕜] G} {u : E × F}
    (hf : HasStrictFDerivAt f D u)
    (hD : (D ∘L ContinuousLinearMap.inr 𝕜 E F).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, ContinuousAt (hf.implicitFunctionOfProdDomain hD) x := by
  let d := hf.implicitFunctionDataOfProdDomain hD
  have htarget : ∀ᶠ x in 𝓝 u.1, (f u, x) ∈ d.toOpenPartialHomeomorph.target := by
    have ht := d.toOpenPartialHomeomorph.open_target.mem_nhds
      d.map_pt_mem_toOpenPartialHomeomorph_target
    exact (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds ht
  filter_upwards [htarget] with x hx
  exact ((d.toOpenPartialHomeomorph.symm.continuousAt hx).comp
    (continuousAt_const.prodMk continuousAt_id)).snd

end NLAlib

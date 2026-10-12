import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Commuting compressions modulo a common invariant orthogonal complement

Compression onto `W` models the quotient by `Wᗮ` whenever that complement is
invariant. It therefore preserves commutation of endomorphisms.
-/

noncomputable section
open Module

namespace NLAlib

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (W : Submodule 𝕜 E) [W.HasOrthogonalProjection]

/-- Projecting before an endomorphism does not change its projected output
when the discarded orthogonal complement is invariant. Quotient-space
identity; helper for `simultaneous-diagonalization`. -/
theorem orthogonalProjectionOnto_map_starProjection_eq
    (f : Module.End 𝕜 E) (hf : Set.MapsTo f Wᗮ Wᗮ) (x : E) :
    W.orthogonalProjectionOnto (f (W.starProjection x)) = W.orthogonalProjectionOnto (f x) := by
  have hzero : W.orthogonalProjectionOnto (f (x - W.starProjection x)) = 0 :=
    W.orthogonalProjectionOnto_eq_zero_iff.mpr (hf (W.sub_starProjection_mem_orthogonal x))
  rw [map_sub, map_sub] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Compressing two commuting operators onto the orthogonal complement
of a common invariant subspace preserves their commutation. Quotient-space
identity; helper for `simultaneous-diagonalization`. -/
theorem commute_orthogonal_compressions_of_invariant
    (f g : Module.End 𝕜 E) (hf : Set.MapsTo f Wᗮ Wᗮ) (hg : Set.MapsTo g Wᗮ Wᗮ)
    (hcomm : Commute f g) :
    Commute (W.orthogonalProjectionOnto.toLinearMap.comp (f.comp W.subtype))
      (W.orthogonalProjectionOnto.toLinearMap.comp (g.comp W.subtype)) := by
  apply LinearMap.ext
  intro x
  change W.orthogonalProjectionOnto (f (W.starProjection (g x.val))) =
    W.orthogonalProjectionOnto (g (W.starProjection (f x.val)))
  rw [orthogonalProjectionOnto_map_starProjection_eq W f hf,
    orthogonalProjectionOnto_map_starProjection_eq W g hg]
  exact congrArg W.orthogonalProjectionOnto (LinearMap.congr_fun hcomm.eq x.val)

end NLAlib

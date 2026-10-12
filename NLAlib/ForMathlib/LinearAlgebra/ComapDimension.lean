import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension of a subspace pulled back by an endomorphism

An endomorphism of a finite dimensional vector space pulls back each subspace
to a subspace of at least the original dimension. Quotient rank--nullity
proves this without an invertibility hypothesis.
-/

noncomputable section
open Module

namespace NLAlib

/-- Pullback by an endomorphism cannot lower a subspace's dimension.
Quotient rank--nullity; helper for `ostrowski-congruence-eigenvalues`. -/
theorem finrank_le_finrank_comap_endomorphism {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Submodule K V) (T : V →ₗ[K] V) :
    finrank K W ≤ finrank K (W.comap T) := by
  have h := LinearMap.finrank_range_add_finrank_ker (W.mkQ.comp T)
  have hr : finrank K (LinearMap.range (W.mkQ.comp T)) ≤ finrank K (V ⧸ W) :=
    (LinearMap.range (W.mkQ.comp T)).finrank_le
  have hW := W.finrank_quotient_add_finrank
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h
  omega

end NLAlib

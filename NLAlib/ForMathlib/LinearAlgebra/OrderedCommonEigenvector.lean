import NLAlib.ForMathlib.LinearAlgebra.CommonEigenvector
/-!
# Common eigenvectors with one prescribed eigenvalue

Restrict an arbitrary commuting family to the designated member's eigenspace,
then find a common eigenvector within that nonzero invariant space.
-/

noncomputable section
open Module
namespace NLAlib

/-- A commuting family has a common nonzero eigenvector inside any
specified nonzero eigenspace of one designated member. The family may be
infinite, and the eigenvalue may have any multiplicity. Horn–Johnson 2013,
Theorem 2.3.3; the prescribed-order strengthening in derivations gen:simultaneous. -/
theorem exists_common_eigenvector_with_eigenvalue
    {K E ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (T : ι → Module.End K E)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (a₀ : ι) (μ : K)
    (hμ : (T a₀).HasEigenvalue μ) :
    ∃ x : E, ∃ χ : ι → K, x ≠ 0 ∧ (∀ a, T a x = χ a • x) ∧ T a₀ x = μ • x := by
  classical
  let W := Module.End.eigenspace (T a₀) μ
  have hW : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hpres (a : ι) : Set.MapsTo (T a) W W := by
    apply Module.End.mapsTo_genEigenspace_of_comm
    rcases eq_or_ne a₀ a with rfl | hne
    · exact Commute.refl _
    · exact hcomm hne
  let S (a : ι) : Module.End K W := (T a).restrict (hpres a)
  have hScomm : Pairwise fun a b => Commute (S a) (S b) := by
    intro a b hab
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (hcomm hab).eq x.val
  obtain ⟨x, χ, hx, hTx⟩ := exists_common_eigenvector_of_pairwise_commute S hScomm
  refine ⟨x.val, χ, fun h => hx (Subtype.ext h), fun a => congrArg Subtype.val (hTx a), ?_⟩
  exact Module.End.mem_eigenspace_iff.mp x.property

end NLAlib

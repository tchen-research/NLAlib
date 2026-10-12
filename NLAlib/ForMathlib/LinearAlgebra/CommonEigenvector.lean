import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A common eigenvector for an arbitrary commuting family

Restrict to a proper eigenspace of a nonscalar member and induct on dimension.
The family need not be finite or nonempty.
Source: Horn–Johnson (2013), Lemma 1.3.19.
-/

noncomputable section
open Module

namespace NLAlib

/-- Every commuting family on a nonzero finite-dimensional vector space
over an algebraically closed field has a common nonzero eigenvector.
Source: Horn–Johnson (2013), Lemma 1.3.19; arbitrary, infinite and empty
families are allowed. -/
theorem exists_common_eigenvector_of_pairwise_commute
    {K E ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Nontrivial E] (f : ι → Module.End K E)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) :
    ∃ (x : E) (χ : ι → K), x ≠ 0 ∧ ∀ i, f i x = χ i • x := by
  classical
  generalize hd : finrank K E = d
  induction d using Nat.strongRecOn generalizing E with
  | ind d ih =>
    by_cases hscalar : ∀ i, ∃ μ, Module.End.eigenspace (f i) μ = ⊤
    · choose χ hχ using hscalar
      obtain ⟨x, hx⟩ := exists_ne (0 : E)
      refine ⟨x, χ, hx, fun i => Module.End.mem_eigenspace_iff.mp ?_⟩
      rw [hχ i]
      trivial
    · push Not at hscalar
      obtain ⟨i, hi⟩ := hscalar
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f i)
      let W := Module.End.eigenspace (f i) μ
      have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
      let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
      have hWdim : finrank K W < d := by
        rw [← hd]
        exact Submodule.finrank_lt (hi μ)
      have hpres (j : ι) : Set.MapsTo (f j) W W := by
        apply Module.End.mapsTo_genEigenspace_of_comm
        rcases eq_or_ne i j with rfl | hij
        · exact Commute.refl _
        · exact hcomm hij
      let g (j : ι) : Module.End K W := (f j).restrict (hpres j)
      have hgcomm : Pairwise fun j k => Commute (g j) (g k) := by
        intro j k hjk
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (hcomm hjk).eq x.val
      obtain ⟨x, χ, hx, hxg⟩ := ih (finrank K W) hWdim g hgcomm rfl
      refine ⟨x.val, χ, fun hx0 => hx (Subtype.ext hx0), fun j => ?_⟩
      exact congrArg Subtype.val (hxg j)

end NLAlib

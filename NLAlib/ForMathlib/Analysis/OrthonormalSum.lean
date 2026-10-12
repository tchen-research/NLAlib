import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Joining orthonormal bases of orthogonal subspaces

An orthonormal basis of a subspace and one of its orthogonal complement
combine without changing any supplied vector. This supports real Schur and QZ.
-/

noncomputable section
open Module
open scoped InnerProductSpace
namespace NLAlib

/-- The orthogonal direct sum of two supplied bases is an orthonormal basis
of the ambient space, with the exact original vectors on each summand.
Horn–Johnson 2013, Section 2.1; real Schur and QZ block-completion helper. -/
theorem exists_orthonormalBasis_sum {𝕜 E ι κ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [Fintype ι] [Fintype κ] (P : Submodule 𝕜 E)
    (bP : OrthonormalBasis ι 𝕜 P) (bQ : OrthonormalBasis κ 𝕜 Pᗮ) :
    ∃ b : OrthonormalBasis (ι ⊕ κ) 𝕜 E,
      (∀ i, b (Sum.inl i) = (bP i : E)) ∧
      (∀ i, b (Sum.inr i) = (bQ i : E)) := by
  classical
  let v : ι ⊕ κ → E := Sum.elim (fun i => (bP i : E)) (fun i => (bQ i : E))
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [v] using orthonormal_iff_ite.mp bP.orthonormal i j
      | inr j =>
        have h := Submodule.inner_right_of_mem_orthogonal (bP i).property (bQ j).property
        simpa [v] using h
    | inr i =>
      cases j with
      | inl j =>
        have h := Submodule.inner_left_of_mem_orthogonal (bP j).property (bQ i).property
        simpa [v] using h
      | inr j => simpa [v] using orthonormal_iff_ite.mp bQ.orthonormal i j
  have hdim : Fintype.card (ι ⊕ κ) = finrank 𝕜 E := by
    rw [Fintype.card_sum, ← finrank_eq_card_basis bP.toBasis,
      ← finrank_eq_card_basis bQ.toBasis, P.finrank_add_finrank_orthogonal]
  let c := basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent hdim
  let b := c.toOrthonormalBasis
    (by simpa only [c, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)
  refine ⟨b, fun i => ?_, fun i => ?_⟩ <;>
    simp only [b, Basis.coe_toOrthonormalBasis, c,
      coe_basisOfLinearIndependentOfCardEqFinrank', v, Sum.elim_inl, Sum.elim_inr]

end NLAlib

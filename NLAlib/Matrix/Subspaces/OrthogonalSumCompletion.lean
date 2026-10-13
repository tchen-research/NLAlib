import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Unitary completion with separately labelled block columns

An orthonormal frame extends to a unitary matrix whose first column block is the given frame,
on arbitrary finite labels `p ⊕ q`. Horn–Johnson 2013, §2.1 (Thm 2.1.4); Golub–Van Loan 2013,
§2.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Complete an orthonormal frame `Q : m × p` to a unitary matrix `H : m × (p ⊕ q)` whose
`inl` block is `Q`, whenever `card p + card q = card m`; both Gram identities `HᴴH = I`,
`HHᴴ = I` are supplied, including empty blocks. Horn–Johnson 2013, Thm 2.1.4; supports the
oblique-projector part of `cs-decomposition`. -/
theorem exists_unitary_sum_completion {𝕜 : Type*} [RCLike 𝕜] {m p q : Type*}
    [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (Q : Matrix m p 𝕜) (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card p + Fintype.card q = Fintype.card m) :
    ∃ H : Matrix m (p ⊕ q) 𝕜,
      HasOrthonormalCols H ∧ H * Hᴴ = 1 ∧ H.submatrix id Sum.inl = Q := by
  let e : (p ⊕ q) ≃ m := Fintype.equivOfCardEq (by simpa using hcard)
  let f : p ↪ m := ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  obtain ⟨W, hW, hWQ⟩ := exists_unitary_completion Q hQ f
  let H := W.reindex (Equiv.refl m) e.symm
  refine ⟨H, hW.reindex _ _, ?_, ?_⟩
  · change W.submatrix id e * Wᴴ.submatrix e id = 1
    rw [Matrix.submatrix_mul_equiv W Wᴴ id e id, Matrix.submatrix_id_id]
    exact hW.mul_conjTranspose_self
  · ext i j
    exact hWQ i j

end NLAlib

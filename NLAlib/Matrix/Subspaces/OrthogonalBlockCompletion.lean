import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Orthogonal completion with fixed first columns

Two ambient orthogonal matrices agreeing on their first block differ by an
orthogonal change only in their remaining columns. This is the completion
step of cosine–sine decomposition. Horn–Johnson 2013, Theorem 2.7.1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Two square orthogonal matrices with equal first block-columns differ
by a block-diagonal right multiplier fixing those columns. The remaining
block is itself orthogonal; empty first or second blocks are allowed.
Horn–Johnson 2013, Theorem 2.7.1, completion step.
atlas: cs-decomposition (partial) -/
theorem exists_orthogonal_right_block_of_first_columns_eq {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (X Y : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hX : HasOrthonormalCols X)
    (hY : HasOrthonormalCols Y)
    (hFirst : X.submatrix id Sum.inl = Y.submatrix id Sum.inl) :
    ∃ W : Matrix q q ℝ, HasOrthonormalCols W ∧ X * Matrix.fromBlocks 1 0 0 W = Y := by
  let T := Xᵀ * Y
  have hT : HasOrthonormalCols T := hX.transpose.mul hY
  have hCols : T.submatrix id Sum.inl = (1 : Matrix (p ⊕ q) (p ⊕ q) ℝ).submatrix id Sum.inl := by
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℝ => Xᵀ * M) hFirst
    have hMul (Z : Matrix (p ⊕ q) (p ⊕ q) ℝ) :
        Xᵀ * Z.submatrix id Sum.inl = (Xᵀ * Z).submatrix id Sum.inl := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Xᵀ Z id (Equiv.refl (p ⊕ q)) Sum.inl
    rw [hMul, hMul, show Xᵀ * X = 1 from hX] at h
    exact h.symm
  have h11 : T.toBlocks₁₁ = 1 := by
    ext i j
    change T (Sum.inl i) (Sum.inl j) = (1 : Matrix p p ℝ) i j
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℝ => M (Sum.inl i) j) hCols
    simpa only [Matrix.submatrix_apply, Matrix.one_apply, id_eq, Sum.inl.injEq] using h
  have h21 : T.toBlocks₂₁ = 0 := by
    ext i j
    change T (Sum.inr i) (Sum.inl j) = 0
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℝ => M (Sum.inr i) j) hCols
    simpa only [Matrix.submatrix_apply, Matrix.one_apply, id_eq, Sum.inr_ne_inl,
      ite_false, Matrix.zero_apply] using h
  have hGram : (Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂)ᵀ *
      Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂ = 1 := by
    rw [Matrix.fromBlocks_toBlocks]
    exact hT
  have h12 : T.toBlocks₁₂ = 0 := by
    have h := congrArg Matrix.toBlocks₁₂ hGram
    simpa only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₁₂, h11, h21, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.one_mul, Matrix.zero_mul, add_zero,
      show (1 : Matrix (p ⊕ q) (p ⊕ q) ℝ).toBlocks₁₂ = 0 by ext i j; simp [Matrix.toBlocks₁₂]] using h
  have h22 : HasOrthonormalCols T.toBlocks₂₂ := by
    change T.toBlocks₂₂ᵀ * T.toBlocks₂₂ = 1
    have h := congrArg Matrix.toBlocks₂₂ hGram
    simpa only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₂, h12, Matrix.transpose_zero, Matrix.zero_mul,
      zero_add, show (1 : Matrix (p ⊕ q) (p ⊕ q) ℝ).toBlocks₂₂ = 1 by
        ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]] using h
  refine ⟨T.toBlocks₂₂, h22, ?_⟩
  have hBlocks : T = Matrix.fromBlocks 1 0 0 T.toBlocks₂₂ := by
    exact (Matrix.fromBlocks_toBlocks T).symm.trans
      (by rw [h11, h12, h21])
  rw [← hBlocks]
  change X * (Xᵀ * Y) = Y
  rw [← Matrix.mul_assoc, show X * Xᵀ = 1 from mul_eq_one_comm.mp hX, Matrix.one_mul]

end NLAlib

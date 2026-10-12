import NLAlib.Matrix.Subspaces.ComplexGramIsometry
/-!
# Unitary completion with fixed first columns

Two ambient unitary matrices agreeing on their first block differ by
a unitary change only in their remaining columns. This is the completion
step of cosine–sine decomposition. Horn–Johnson 2013, Theorem 2.7.1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Two square unitary matrices with equal first block-columns differ
by a block-diagonal right multiplier fixing those columns. The remaining
block is itself unitary; empty first or second blocks are allowed.
Horn–Johnson 2013, Theorem 2.7.1, completion step.
atlas: cs-decomposition (partial) -/
theorem exists_unitary_right_block_of_first_columns_eq {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (X Y : Matrix (p ⊕ q) (p ⊕ q) ℂ) (hX : Xᴴ * X = 1)
    (hY : Yᴴ * Y = 1)
    (hFirst : X.submatrix id Sum.inl = Y.submatrix id Sum.inl) :
    ∃ W : Matrix q q ℂ, Wᴴ * W = 1 ∧ X * Matrix.fromBlocks 1 0 0 W = Y := by
  let T := Xᴴ * Y
  have hT : Tᴴ * T = 1 := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc X Xᴴ Y, mul_eq_one_comm.mp hX, Matrix.one_mul, hY]
  have hCols : T.submatrix id Sum.inl = (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ).submatrix id Sum.inl := by
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℂ => Xᴴ * M) hFirst
    have hMul (Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
        Xᴴ * Z.submatrix id Sum.inl = (Xᴴ * Z).submatrix id Sum.inl := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Xᴴ Z id (Equiv.refl (p ⊕ q)) Sum.inl
    rw [hMul, hMul, hX] at h
    exact h.symm
  have h11 : T.toBlocks₁₁ = 1 := by
    ext i j
    change T (Sum.inl i) (Sum.inl j) = (1 : Matrix p p ℂ) i j
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℂ => M (Sum.inl i) j) hCols
    simpa only [Matrix.submatrix_apply, Matrix.one_apply, id_eq, Sum.inl.injEq] using h
  have h21 : T.toBlocks₂₁ = 0 := by
    ext i j
    change T (Sum.inr i) (Sum.inl j) = 0
    have h := congrArg (fun M : Matrix (p ⊕ q) p ℂ => M (Sum.inr i) j) hCols
    simpa only [Matrix.submatrix_apply, Matrix.one_apply, id_eq, Sum.inr_ne_inl,
      ite_false, Matrix.zero_apply] using h
  have hGram : (Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂)ᴴ *
      Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂ = 1 := by
    rw [Matrix.fromBlocks_toBlocks]
    exact hT
  have h12 : T.toBlocks₁₂ = 0 := by
    have h := congrArg Matrix.toBlocks₁₂ hGram
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₁₂, h11, h21, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.one_mul, Matrix.zero_mul, add_zero,
      show (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ).toBlocks₁₂ = 0 by ext i j; simp [Matrix.toBlocks₁₂]] using h
  have h22 : T.toBlocks₂₂ᴴ * T.toBlocks₂₂ = 1 := by
    have h := congrArg Matrix.toBlocks₂₂ hGram
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₂, h12, Matrix.conjTranspose_zero, Matrix.zero_mul,
      zero_add, show (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ).toBlocks₂₂ = 1 by
        ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]] using h
  refine ⟨T.toBlocks₂₂, h22, ?_⟩
  have hBlocks : T = Matrix.fromBlocks 1 0 0 T.toBlocks₂₂ := by
    exact (Matrix.fromBlocks_toBlocks T).symm.trans
      (by rw [h11, h12, h21])
  rw [← hBlocks]
  change X * (Xᴴ * Y) = Y
  rw [← Matrix.mul_assoc, show X * Xᴴ = 1 from mul_eq_one_comm.mp hX, Matrix.one_mul]

end NLAlib

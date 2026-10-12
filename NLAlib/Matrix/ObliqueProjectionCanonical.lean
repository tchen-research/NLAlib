import NLAlib.Matrix.ObliqueProjectionBlocks

/-!
# Orthogonal canonical form of an oblique projection

The off-diagonal block in range-adapted coordinates admits an actual rectangular
SVD. Its positive singular coefficients give the two-dimensional oblique blocks;
all remaining range coordinates are identities and kernel coordinates are zero.
Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Every real idempotent is orthogonally similar to `[I diag(t); 0 0]`,
where `t` is nonnegative, decreasing and positive exactly before `g`.
Pairing these `g` range/kernel coordinates displays the direct sum of
`[1 tᵢ; 0 0]`, an identity of size `rank P - g`, and a zero block of size
`card n - rank P - g`. Zero and full rank are included.
Horn–Johnson 2013, Corollary 3.4.3.3; derivations §alg:cs.
atlas: cs-decomposition (partial) -/
theorem exists_orthogonal_idempotent_canonical {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (hP : IsIdempotentElem P) :
    ∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ,
      HasOrthonormalCols H ∧ H * Hᵀ = 1 ∧
      Hᵀ * P * H = Matrix.fromBlocks 1 (rectDiag t) 0 0 := by
  obtain ⟨H, T, hH, hHt, hBlock⟩ := exists_orthogonal_idempotent_range_blocks P hP
  obtain ⟨V, W, hSVD⟩ := exists_isSVD T
  let K := Matrix.fromBlocks V 0 0 W
  have hK : HasOrthonormalCols K := by
    change (Matrix.fromBlocks V 0 0 W)ᵀ * Matrix.fromBlocks V 0 0 W = 1
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hSVD.transpose_mul_left, hSVD.transpose_mul_right, Matrix.fromBlocks_one]
  refine ⟨T.rank, le_min T.rank_le_height T.rank_le_width,
    singularValues T, singularValues_nonneg T, singularValues_antitone T,
    singularValues_pos_iff T, H * K, hH.mul hK, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc K Kᵀ Hᵀ,
      show K * Kᵀ = 1 from mul_eq_one_comm.mp hK, Matrix.one_mul, hHt]
  · rw [Matrix.transpose_mul]
    calc
      (Kᵀ * Hᵀ) * P * (H * K) = Kᵀ * (Hᵀ * P * H) * K := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks 1 (rectDiag (singularValues T)) 0 0 := by
        rw [hBlock]
        simp only [K, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
          Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
          add_zero, zero_add, Matrix.mul_one, hSVD.transpose_mul_left,
          hSVD.transpose_mul_mul]

end NLAlib

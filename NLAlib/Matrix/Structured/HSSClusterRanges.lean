import NLAlib.Matrix.Structured.HSSCutRanks

/-! # Nested complete-cut ranges supply HSS transfer and coupling spaces -/
noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K N I J P : Type*} [RCLike K] [Fintype N] [DecidableEq N]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
/-- Restricting a parent's complete cut to a child keeps precisely those child
cut columns that were already outside the parent. -/
theorem clusterOffRow_submatrix_embedding (A : Matrix N N K) (e : J ↪ N) (f : I ↪ J) :
    (clusterOffRow A e).submatrix f id = clusterOffRow A (f.trans e) *
      Matrix.diagonal (fun j => if j ∈ Set.range e then (0 : K) else 1) := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, clusterOffRow, Matrix.mul_diagonal, id_eq]
  by_cases hj : j ∈ Set.range e
  · rw [if_pos hj, if_pos hj, mul_zero]
  · have hf : j ∉ Set.range (f.trans e) := by
      rintro ⟨x,hx⟩
      exact hj ⟨f x,hx⟩
    rw [if_neg hj, if_neg hj, if_neg hf, mul_one]
    rfl

/-- A parent cut basis restricts into each child's full cut space. This is
where complete off-diagonal cut ranks provide genuine nested bases. -/
theorem range_cluster_basis_restriction_le (A : Matrix N N K) (e : J ↪ N) (f : I ↪ J)
    (M : Matrix J P K) (hM : LinearMap.range M.mulVecLin ≤ LinearMap.range (clusterOffRow A e).mulVecLin) :
    LinearMap.range (M.submatrix f id).mulVecLin ≤ LinearMap.range (clusterOffRow A (f.trans e)).mulVecLin := by
  have h := range_submatrix_rows_le_of_range_le M (clusterOffRow A e) f hM
  rw [clusterOffRow_submatrix_embedding] at h
  exact h.trans (range_mulVecLin_mul_le _ _)

omit [Fintype N] [DecidableEq N] in
/-- Distinct sibling coordinates lie outside each other's cluster. -/
theorem ClusterTree.right_not_mem_range_left {l r : ClusterTree}
    (e : (ClusterTree.node l r).Index ↪ N) (j : r.Index) :
    ClusterTree.rightEmbedding e j ∉ Set.range (ClusterTree.leftEmbedding e) := by
  rintro ⟨i,hi⟩
  have h := e.injective hi
  exact Sum.inl_ne_inr h

/-- A sibling interaction is literally a selection of the complete cut's
outside columns. -/
theorem clusterOffRow_left_sibling {l r : ClusterTree} (A : Matrix N N K)
    (e : (ClusterTree.node l r).Index ↪ N) :
    (clusterOffRow A (ClusterTree.leftEmbedding e)).submatrix id (ClusterTree.rightEmbedding e) =
      A.submatrix (ClusterTree.leftEmbedding e) (ClusterTree.rightEmbedding e) := by
  ext i j
  simp only [Matrix.submatrix_apply, clusterOffRow, id_eq]
  rw [if_neg (ClusterTree.right_not_mem_range_left e j)]

/-- A sibling block's columns belong to the complete left-child cut space. -/
theorem range_left_sibling_le {l r : ClusterTree} (A : Matrix N N K)
    (e : (ClusterTree.node l r).Index ↪ N) :
    LinearMap.range (A.submatrix (ClusterTree.leftEmbedding e) (ClusterTree.rightEmbedding e)).mulVecLin ≤
      LinearMap.range (clusterOffRow A (ClusterTree.leftEmbedding e)).mulVecLin := by
  rw [← clusterOffRow_left_sibling]
  exact range_submatrix_cols_le _ _

/-- The reverse sibling interaction has the same full-cut interpretation. -/
theorem range_right_sibling_le {l r : ClusterTree} (A : Matrix N N K)
    (e : (ClusterTree.node l r).Index ↪ N) :
    LinearMap.range (A.submatrix (ClusterTree.rightEmbedding e) (ClusterTree.leftEmbedding e)).mulVecLin ≤
      LinearMap.range (clusterOffRow A (ClusterTree.rightEmbedding e)).mulVecLin := by
  have he : (clusterOffRow A (ClusterTree.rightEmbedding e)).submatrix id (ClusterTree.leftEmbedding e) =
      A.submatrix (ClusterTree.rightEmbedding e) (ClusterTree.leftEmbedding e) := by
    ext i j
    have hn : ClusterTree.leftEmbedding e j ∉ Set.range (ClusterTree.rightEmbedding e) := by
      rintro ⟨x,hx⟩
      exact Sum.inr_ne_inl (e.injective hx)
    simp only [Matrix.submatrix_apply, clusterOffRow, id_eq]
    rw [if_neg hn]
  rw [← he]
  exact range_submatrix_cols_le _ _

end NLAlib

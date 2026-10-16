import NLAlib.Matrix.Structured.ClusterTree
import NLAlib.Matrix.Structured.InverseCutRank
import NLAlib.Matrix.Basic.ColumnSpaceFactorization

/-! # Actual whole-cluster off-diagonal cuts on a binary partition tree -/
noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K N : Type*} [RCLike K] [Fintype N] [DecidableEq N]

/-- Embed the left child into the same global coordinates as its parent. -/
def ClusterTree.leftEmbedding {l r : ClusterTree} (e : (ClusterTree.node l r).Index ↪ N) : l.Index ↪ N :=
  ⟨fun i => e (Sum.inl i), fun _ _ h => Sum.inl_injective (e.injective h)⟩

/-- Embed the right child into the parent's global coordinates. -/
def ClusterTree.rightEmbedding {l r : ClusterTree} (e : (ClusterTree.node l r).Index ↪ N) : r.Index ↪ N :=
  ⟨fun i => e (Sum.inr i), fun _ _ h => Sum.inr_injective (e.injective h)⟩

/-- The complete off-diagonal block row for a cluster. Ambient columns inside
the cluster are explicitly zero; this zero padding preserves the cut rank. -/
def clusterOffRow {I : Type*} (A : Matrix N N K) (e : I ↪ N) : Matrix I N K := by
  classical
  exact fun i j => if j ∈ Set.range e then 0 else A (e i) j

/-- Zero padding changes neither the actual whole-cut rank nor its meaning. -/
theorem rank_clusterOffRow_eq_cut {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix N N K) (e : I ↪ N) :
    (clusterOffRow A e).rank = (A.toBlock (fun j => j ∈ Set.range e) (fun j => j ∉ Set.range e)).rank := by
  classical
  let f : I ≃ {j // j ∈ Set.range e} := Equiv.ofInjective e e.injective
  let J := (clusterOffRow A e).submatrix f.symm id
  have hspan : Submodule.span K (Set.range J.col) =
      Submodule.span K (Set.range (A.toBlock (fun j => j ∈ Set.range e) (fun j => j ∉ Set.range e)).col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      by_cases hj : j ∈ Set.range e
      · have hz : J.col j = 0 := by ext i; simp [J, clusterOffRow, hj]
        rw [hz]
        exact Submodule.zero_mem _
      · have hc : J.col j = (A.toBlock (fun j => j ∈ Set.range e) (fun j => j ∉ Set.range e)).col ⟨j,hj⟩ := by
          ext i
          have hi : e (f.symm i) = i.val := congrArg Subtype.val (f.apply_symm_apply i)
          simp [J, clusterOffRow, hj, Matrix.toBlock, Matrix.col, hi]
        rw [hc]
        exact Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      have hc : (A.toBlock (fun j => j ∈ Set.range e) (fun j => j ∉ Set.range e)).col j = J.col j.val := by
        ext i
        have hi : e (f.symm i) = i.val := congrArg Subtype.val (f.apply_symm_apply i)
        simp [J, clusterOffRow, j.property, Matrix.toBlock, Matrix.col, hi]
      rw [hc]
      exact Submodule.subset_span ⟨j.val,rfl⟩
  calc
    _ = J.rank := (Matrix.rank_submatrix _ f.symm (Equiv.refl _)).symm
    _ = _ := by rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]

/-- Every cluster's two directed whole-cut ranks, recursively over the actual
partition tree. This is stronger than bounding sibling blocks alone. -/
def HasHSSCutRanks (A : Matrix N N K) (k : ℕ) : (t : ClusterTree) → (t.Index ↪ N) → Prop
  | .leaf _, e => (clusterOffRow A e).rank ≤ k ∧ (clusterOffRow Aᴴ e).rank ≤ k
  | .node l r, e =>
      (clusterOffRow A e).rank ≤ k ∧ (clusterOffRow Aᴴ e).rank ≤ k ∧
      HasHSSCutRanks A k l (ClusterTree.leftEmbedding e) ∧
      HasHSSCutRanks A k r (ClusterTree.rightEmbedding e)

omit [DecidableEq N] in
/-- The current cluster inherits its actual row and column cut bounds. -/
theorem HasHSSCutRanks.here {A : Matrix N N K} {k : ℕ} {t : ClusterTree}
    {e : t.Index ↪ N} (h : HasHSSCutRanks A k t e) :
    (clusterOffRow A e).rank ≤ k ∧ (clusterOffRow Aᴴ e).rank ≤ k := by
  cases t with
  | leaf _ => simpa only [HasHSSCutRanks] using h
  | node _ _ => exact ⟨h.1,h.2.1⟩

/-- Inversion preserves every actual whole-cluster cut rank simultaneously,
without any principal-pivot assumption. -/
theorem HasHSSCutRanks.inv {A : Matrix N N K} {k : ℕ} {t : ClusterTree}
    {e : t.Index ↪ N} (h : HasHSSCutRanks A k t e) (hA : IsUnit A.det) :
    HasHSSCutRanks A⁻¹ k t e := by
  have hrow {I : Type} [Fintype I] [DecidableEq I] (M : Matrix N N K)
      (hM : IsUnit M.det) (f : I ↪ N) : (clusterOffRow M⁻¹ f).rank = (clusterOffRow M f).rank := by
    classical
    rw [rank_clusterOffRow_eq_cut, rank_clusterOffRow_eq_cut]
    exact rank_inverse_toBlock_complement_eq M hM (fun j => j ∈ Set.range f)
  induction t with
  | leaf _ =>
    exact ⟨(hrow A hA e).trans_le h.1, by
      rw [Matrix.conjTranspose_nonsing_inv, hrow Aᴴ (by simpa [Matrix.det_conjTranspose] using hA.star) e]
      exact h.2⟩
  | node l r hl hr =>
    exact ⟨(hrow A hA e).trans_le h.1, by
      rw [Matrix.conjTranspose_nonsing_inv, hrow Aᴴ (by simpa [Matrix.det_conjTranspose] using hA.star) e]
      exact h.2.1, hl h.2.2.1, hr h.2.2.2⟩

end NLAlib

import NLAlib.Matrix.Structured.HSS
import NLAlib.Matrix.Structured.HSSClusterRanges
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Exact nested HSS representations from complete cut ranks

Range-preserving bases of the complete off-diagonal cut rows restrict into
child cut spaces. These inclusions construct actual transfer matrices and
two-sided sibling couplings, without any principal-block invertibility.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K N : Type*} [RCLike K] [Fintype N] [DecidableEq N]

/-- Complete row and column cut-rank bounds construct an actual nested HSS
representation with those cut spaces as its root basis ranges. -/
theorem exists_hss_of_cutRanks (A : Matrix N N K) (k : ℕ) (t : ClusterTree)
    (e : t.Index ↪ N) (h : HasHSSCutRanks A k t e) :
    ∃ H : HSS K t k, H.matrix = A.submatrix e e ∧ H.RanksLE k ∧
      LinearMap.range H.rowBasis.mulVecLin = LinearMap.range (clusterOffRow A e).mulVecLin ∧
      LinearMap.range H.colBasis.mulVecLin = LinearMap.range (clusterOffRow Aᴴ e).mulVecLin := by
  classical
  induction t with
  | leaf z =>
    obtain ⟨U,T,hT,hU⟩ := exists_mul_range_eq_of_rank_le (clusterOffRow A e) k h.1
    obtain ⟨V,S,hS,hV⟩ := exists_mul_range_eq_of_rank_le (clusterOffRow Aᴴ e) k h.2
    exact ⟨HSS.leaf (A.submatrix e e) U V, rfl, le_rfl, hU,hV⟩
  | node l r hl hr =>
    obtain ⟨L,hL,hLrank,hLU,hLV⟩ := hl (ClusterTree.leftEmbedding e) h.2.2.1
    obtain ⟨R,hR,hRrank,hRU,hRV⟩ := hr (ClusterTree.rightEmbedding e) h.2.2.2
    obtain ⟨U,T,hT,hU⟩ := exists_mul_range_eq_of_rank_le (clusterOffRow A e) k h.1
    obtain ⟨V,S,hS,hV⟩ := exists_mul_range_eq_of_rank_le (clusterOffRow Aᴴ e) k h.2.1
    let fl : l.Index ↪ (ClusterTree.node l r).Index := ⟨Sum.inl,Sum.inl_injective⟩
    let fr : r.Index ↪ (ClusterTree.node l r).Index := ⟨Sum.inr,Sum.inr_injective⟩
    have hUl : LinearMap.range (U.submatrix Sum.inl id).mulVecLin ≤ LinearMap.range L.rowBasis.mulVecLin := by
      rw [hLU]
      exact range_cluster_basis_restriction_le A e fl U hU.le
    have hUr : LinearMap.range (U.submatrix Sum.inr id).mulVecLin ≤ LinearMap.range R.rowBasis.mulVecLin := by
      rw [hRU]
      exact range_cluster_basis_restriction_le A e fr U hU.le
    have hVl : LinearMap.range (V.submatrix Sum.inl id).mulVecLin ≤ LinearMap.range L.colBasis.mulVecLin := by
      rw [hLV]
      exact range_cluster_basis_restriction_le Aᴴ e fl V hV.le
    have hVr : LinearMap.range (V.submatrix Sum.inr id).mulVecLin ≤ LinearMap.range R.colBasis.mulVecLin := by
      rw [hRV]
      exact range_cluster_basis_restriction_le Aᴴ e fr V hV.le
    obtain ⟨El,hEl⟩ := exists_mul_of_range_le L.rowBasis (U.submatrix Sum.inl id) hUl
    obtain ⟨Er,hEr⟩ := exists_mul_of_range_le R.rowBasis (U.submatrix Sum.inr id) hUr
    obtain ⟨Fl,hFl⟩ := exists_mul_of_range_le L.colBasis (V.submatrix Sum.inl id) hVl
    obtain ⟨Fr,hFr⟩ := exists_mul_of_range_le R.colBasis (V.submatrix Sum.inr id) hVr
    have hBl : LinearMap.range (A.submatrix (ClusterTree.leftEmbedding e) (ClusterTree.rightEmbedding e)).mulVecLin ≤
        LinearMap.range L.rowBasis.mulVecLin := by rw [hLU]; exact range_left_sibling_le A e
    have hBr : LinearMap.range (A.submatrix (ClusterTree.leftEmbedding e) (ClusterTree.rightEmbedding e))ᴴ.mulVecLin ≤
        LinearMap.range R.colBasis.mulVecLin := by
      rw [Matrix.conjTranspose_submatrix, hRV]
      exact range_right_sibling_le Aᴴ e
    obtain ⟨B,hB⟩ := exists_mul_mul_conjTranspose_of_ranges L.rowBasis R.colBasis _ hBl hBr
    have hCl : LinearMap.range (A.submatrix (ClusterTree.rightEmbedding e) (ClusterTree.leftEmbedding e)).mulVecLin ≤
        LinearMap.range R.rowBasis.mulVecLin := by rw [hRU]; exact range_right_sibling_le A e
    have hCr : LinearMap.range (A.submatrix (ClusterTree.rightEmbedding e) (ClusterTree.leftEmbedding e))ᴴ.mulVecLin ≤
        LinearMap.range L.colBasis.mulVecLin := by
      rw [Matrix.conjTranspose_submatrix, hLV]
      exact range_left_sibling_le Aᴴ e
    obtain ⟨C,hC⟩ := exists_mul_mul_conjTranspose_of_ranges R.rowBasis L.colBasis _ hCl hCr
    let H : HSS K (.node l r) k := HSS.node L R (Matrix.fromRows El Er) (Matrix.fromRows Fl Fr) B C
    have hrow : H.rowBasis = U := by
      change Matrix.fromBlocks L.rowBasis 0 0 R.rowBasis * Matrix.fromRows El Er = U
      rw [Matrix.fromBlocks_mul_fromRows]
      simp only [Matrix.zero_mul, zero_add, add_zero]
      rw [← hEl, ← hEr]
      ext i j
      cases i <;> rfl
    have hcol : H.colBasis = V := by
      change Matrix.fromBlocks L.colBasis 0 0 R.colBasis * Matrix.fromRows Fl Fr = V
      rw [Matrix.fromBlocks_mul_fromRows]
      simp only [Matrix.zero_mul, zero_add, add_zero]
      rw [← hFl, ← hFr]
      ext i j
      cases i <;> rfl
    refine ⟨H,?_,⟨le_rfl,hLrank,hRrank⟩,?_,?_⟩
    · change Matrix.fromBlocks L.matrix (L.rowBasis * B * R.colBasisᴴ)
        (R.rowBasis * C * L.colBasisᴴ) R.matrix = A.submatrix e e
      rw [hL,hR,← hB,← hC]
      ext i j
      cases i <;> cases j <;> rfl
    · rw [hrow]
      exact hU
    · rw [hcol]
      exact hV

private def HSS.clearRoot {t : ClusterTree} {r : ℕ} : HSS K t r → HSS K t 0
  | .leaf D _ _ => HSS.leaf D 0 0
  | .node L R _ _ B C => HSS.node L R 0 0 B C

private theorem HSS.matrix_clearRoot {t : ClusterTree} {r : ℕ} (H : HSS K t r) :
    H.clearRoot.matrix = H.matrix := by cases H <;> rfl

private theorem HSS.ranksLE_clearRoot {t : ClusterTree} {r k : ℕ} (H : HSS K t r)
    (h : H.RanksLE k) : H.clearRoot.RanksLE k := by
  cases H with
  | leaf _ _ _ => exact Nat.zero_le k
  | node L R E F B C => exact ⟨Nat.zero_le k,h.2.1,h.2.2⟩

/-- Whole-cut rank bounds construct an exact representation with an empty
root basis and all internal nested ranks bounded by `k`. -/
theorem exists_hss_root_zero_of_cutRanks (t : ClusterTree) (A : Matrix t.Index t.Index K) (k : ℕ) (h : HasHSSCutRanks A k t (Function.Embedding.refl _)) :
    ∃ H : HSS K t 0, H.matrix = A ∧ H.RanksLE k := by
  obtain ⟨H,hH,hRank,-,-⟩ := exists_hss_of_cutRanks A k t (Function.Embedding.refl _) h
  exact ⟨H.clearRoot, (H.matrix_clearRoot.trans hH), H.ranksLE_clearRoot hRank⟩

/-- Inversion preserves exact HSS cut ranks and admits an actual nested HSS
representation on the same partition tree, without invertible principal
blocks or elimination pivots. Source: user derivations, complementary
nullities and nested complete-cut bases.
atlas: hss-inverse-rank-preservation -/
theorem exists_hss_inverse_of_cutRanks (t : ClusterTree) (A : Matrix t.Index t.Index K)
    (k : ℕ) (hA : IsUnit A.det)
    (h : HasHSSCutRanks A k t (Function.Embedding.refl _)) :
    ∃ H : HSS K t 0, H.matrix = A⁻¹ ∧ H.RanksLE k :=
  exists_hss_root_zero_of_cutRanks t A⁻¹ k (h.inv hA)

end NLAlib

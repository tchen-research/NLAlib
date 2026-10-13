import NLAlib.Matrix.Spectral.SVD
import NLAlib.Matrix.Spectral.EigenvalueEquality
import NLAlib.Matrix.Norms.Reindex

/-!
# Singular values under reindexing

Sorted eigenvalues `eigenvalues₀` are invariant under relabeling and do not depend on the
Hermitian witness (`NLAlib.Matrix.Spectral.EigenvalueEquality`); hence `singularValues`
(whose squares are the sorted Gram eigenvalues, `sq_singularValues_eq_eigenvalues₀`) is
invariant under reindexing rows and columns. As a first consequence, the Frobenius identity
`‖A‖_F² = ∑_{k < min m n} σ_k²` (`frobSq_eq_sum_sq_singularValues`) holds on arbitrary finite
index types.
Source: Horn–Johnson 2013, Section 2.6; supports `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Relabeling the rows and columns of a matrix (over `ℝ` or `ℂ`) by equivalences preserves
every singular value, including the padded zeros. Horn–Johnson 2013, Section 2.6, unitary
coordinate changes (permutation matrices). -/
theorem singularValues_reindex {m n p q 𝕜 : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n 𝕜)
    (em : m ≃ p) (en : n ≃ q) :
    singularValues (A.reindex em en) = singularValues A := by
  classical
  funext k
  by_cases hk : k < Fintype.card n
  · have hkq : k < Fintype.card q := by simpa only [← Fintype.card_congr en] using hk
    have hgram : ((A.reindex em en)ᴴ * (A.reindex em en)) = (Aᴴ * A).reindex en en := by
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv]
    have hs : singularValues (A.reindex em en) k ^ 2 = singularValues A k ^ 2 := by
      rw [sq_singularValues_eq_eigenvalues₀ _ ⟨k, hkq⟩,
        sq_singularValues_eq_eigenvalues₀ _ ⟨k, hk⟩]
      exact (congrFun (eigenvalues₀_eq_of_matrix_eq _ _ hgram) ⟨k, hkq⟩).trans
        (eigenvalues₀_reindex (Matrix.isHermitian_conjTranspose_mul_self A) en ⟨k, hk⟩)
    nlinarith [singularValues_nonneg (A.reindex em en) k, singularValues_nonneg A k]
  · rw [singularValues_eq_linearMap, singularValues_eq_linearMap,
      LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    · simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk
    · simpa only [finrank_euclideanSpace, ← Fintype.card_congr en] using Nat.le_of_not_gt hk

/-- `‖A‖_F² = ∑_{k < min m n} σ_k²` on arbitrary finite index types, over `ℝ` or `ℂ`
(Horn–Johnson 2013, §2.6 / 5.6; HMT 2011, §2.1). Atlas `svd`.
atlas: svd -/
theorem frobSq_eq_sum_sq_singularValues {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n 𝕜) :
    frobSq A = ∑ k ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A k ^ 2 := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A
  rw [frobSq, frobInner_eq_trace, h.conjTranspose_mul_self, Matrix.trace_mul_cycle,
    h.conjTranspose_mul_right, Matrix.one_mul, Matrix.trace_diagonal, map_sum]
  simp only [RCLike.ofReal_re]
  rw [Fin.sum_univ_eq_sum_range (fun k => singularValues A k ^ 2)]
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk
    rw [singularValues_eq_zero_of_min_le A
      (by simp only [Finset.mem_range, min_le_iff] at hk ⊢; omega)]; simp

end NLAlib

import NLAlib.Matrix.Spectral.SVD

/-!
# Sorted Gram spectra under relabeling, and singular values under reindexing

Sorted eigenvalues `eigenvalues₀` are invariant under relabeling and do not depend on the
Hermitian witness; hence `singularValues` (whose squares are the sorted Gram eigenvalues,
`sq_singularValues_eq_eigenvalues₀`) is invariant under reindexing rows and columns.
Source: Horn–Johnson 2013, Section 2.6; supports `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Sorted eigenvalues are invariant under equivalent labels, with the canonical
dimension cast. Horn–Johnson 2013, permutation similarity; multiplicities included.
-/
theorem eigenvalues₀_reindex {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (e : n ≃ p) (i : Fin (Fintype.card n)) :
    (hA.reindex e).eigenvalues₀ (Fin.cast (Fintype.card_congr e) i) = hA.eigenvalues₀ i := by
  have hl : List.ofFn (hA.reindex e).eigenvalues₀ = List.ofFn hA.eigenvalues₀ := by
    rw [← (hA.reindex e).sort_roots_charpoly_eq_eigenvalues₀,
      ← hA.sort_roots_charpoly_eq_eigenvalues₀, Matrix.charpoly_reindex]
  have hc := List.ofFn_congr (Fintype.card_congr e) hA.eigenvalues₀
  have hf := List.ofFn_inj.mp (hl.trans hc)
  simpa only [Fin.cast] using congrFun hf (Fin.cast (Fintype.card_congr e) i)

/-- Equal real Hermitian matrices have identical sorted eigenvalues, independent
of their Hermitian witnesses. Mathlib's sorted spectral construction; no nonempty
or simple-spectrum condition is needed. -/
theorem eigenvalues₀_eq_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i : Fin (Fintype.card n)) : hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
  subst h
  rfl

/-- Relabeling the rows and columns of a real matrix by equivalences preserves every
singular value, including the padded zeros. Horn–Johnson 2013, Section 2.6, orthogonal
coordinate changes (permutation matrices). -/
theorem singularValues_reindex {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ)
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
      exact (eigenvalues₀_eq_of_eq hgram _ _ ⟨k, hkq⟩).trans
        (eigenvalues₀_reindex (Matrix.isHermitian_conjTranspose_mul_self A) en ⟨k, hk⟩)
    nlinarith [singularValues_nonneg (A.reindex em en) k, singularValues_nonneg A k]
  · rw [singularValues_eq_linearMap, singularValues_eq_linearMap,
      LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    · simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk
    · simpa only [finrank_euclideanSpace, ← Fintype.card_congr en] using Nat.le_of_not_gt hk

end NLAlib

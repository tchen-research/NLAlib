import NLAlib.Matrix.Spectral.SVD
import Mathlib.Analysis.Matrix.PosDef

/-!
# Native singular values and the sorted matrix Gram spectrum

The square of each domain-indexed singular value is the corresponding sorted
Gram eigenvalue. The statement uses Mathlib's native linear-map singular values
on arbitrary finite matrix indices, including all domain-side padded zeros.
Source: Horn–Johnson 2013, Section 2.6; supports `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

private theorem symmetric_eigenvalues_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T S : E →ₗ[ℝ] E}
    (h : T = S) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {d : ℕ} (hn : Module.finrank ℝ E = d) (i : Fin d) :
    hT.eigenvalues hn i = hS.eigenvalues hn i := by
  subst h
  rfl

/-- The squares of native domain-indexed singular values are the sorted Gram
eigenvalues, on arbitrary finite real matrix indices. Horn–Johnson 2013, Section 2.6.
-/
theorem sq_toEuclideanLin_singularValues_eq_eigenvalues₀ {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ)
    (i : Fin (Fintype.card n)) :
    (A.toEuclideanLin.singularValues (i : ℕ)) ^ 2 =
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ i := by
  classical
  have heq : LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin =
      (Aᴴ * A).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  have hi := A.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace i
  change _ = (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_conjTranspose_mul_self A)).eigenvalues finrank_euclideanSpace i
  rw [hi]
  exact symmetric_eigenvalues_congr heq _ _ finrank_euclideanSpace i

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

/-- Equivalent matrix row and column labels preserve Mathlib's actual native
singular values at every natural index, including padded zero indices.
Horn–Johnson 2013, Section 2.6, orthogonal coordinate changes.
-/
theorem toEuclideanLin_singularValues_reindex {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ)
    (em : m ≃ p) (en : n ≃ q) (k : ℕ) :
    (A.reindex em en).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  classical
  by_cases hk : k < Fintype.card n
  · have hkq : k < Fintype.card q := by simpa only [← Fintype.card_congr en] using hk
    have hgram : ((A.reindex em en)ᴴ * (A.reindex em en)) = (Aᴴ * A).reindex en en := by
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv]
    have hs : ((A.reindex em en).toEuclideanLin.singularValues k) ^ 2 =
        (A.toEuclideanLin.singularValues k) ^ 2 := by
      rw [sq_toEuclideanLin_singularValues_eq_eigenvalues₀ _ ⟨k, hkq⟩,
        sq_toEuclideanLin_singularValues_eq_eigenvalues₀ _ ⟨k, hk⟩]
      exact (eigenvalues₀_eq_of_eq hgram _ _ ⟨k, hkq⟩).trans
        (eigenvalues₀_reindex (Matrix.isHermitian_conjTranspose_mul_self A) en ⟨k, hk⟩)
    nlinarith [(A.reindex em en).toEuclideanLin.singularValues_nonneg k,
      A.toEuclideanLin.singularValues_nonneg k]
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    · simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk
    · simpa only [finrank_euclideanSpace, ← Fintype.card_congr en] using Nat.le_of_not_gt hk

/-- The explicit finite-index normalization agrees with the native matrix
singular values. Horn–Johnson 2013, Section 2.6; every natural index is included.
-/
theorem singularValues_reindex_eq_toEuclideanLin_singularValues {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (k : ℕ) :
    singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k =
      A.toEuclideanLin.singularValues k :=
  toEuclideanLin_singularValues_reindex A (Fintype.equivFin m) (Fintype.equivFin n) k

end NLAlib

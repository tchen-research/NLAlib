import NLAlib.Matrix.Spectral.Weyl
import NLAlib.Matrix.Basic.RankBounds
import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Weyl's multiplicative singular-value inequality

The explicit low-rank competitor obtained from the two truncated SVDs proves
the product inequality at all natural indices, including padded zeros, first for
`Fin`-indexed matrices and then on arbitrary finite index types by reindexing.
Source: Horn–Johnson 1991, Theorem 3.3.16(d). Atlas: `weyl-product-singular-values`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Weyl's product inequality for `Fin`-indexed matrices (base case of
`singularValues_mul_add_le`), via the two truncated SVDs. -/
private theorem singularValues_mul_add_le_fin {m p n : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) (i j : ℕ) :
    singularValues (A * B) (i + j) ≤ singularValues A i * singularValues B j := by
  let C := truncatedSVD A i * B + (A - truncatedSVD A i) * truncatedSVD B j
  have hC : C.rank ≤ i + j :=
    (rank_add_le _ _).trans (Nat.add_le_add
      ((Matrix.rank_mul_le_left _ _).trans (isBestRankApprox_truncatedSVD A i).1)
      ((Matrix.rank_mul_le_right _ _).trans (isBestRankApprox_truncatedSVD B j).1))
  have hdiff : A * B - C = (A - truncatedSVD A i) * (B - truncatedSVD B j) := by
    simp only [C, Matrix.sub_mul, Matrix.mul_sub]
    abel
  calc
    singularValues (A * B) (i + j) ≤ specNorm (A * B - C) :=
      singularValues_le_specNorm_sub_of_rank_le _ _ hC
    _ = specNorm ((A - truncatedSVD A i) * (B - truncatedSVD B j)) := by rw [hdiff]
    _ ≤ specNorm (A - truncatedSVD A i) * specNorm (B - truncatedSVD B j) :=
      specNorm_mul_le _ _
    _ = singularValues A i * singularValues B j := by
      rw [specNorm_sub_truncatedSVD_eq, specNorm_sub_truncatedSVD_eq]

/-- Weyl's product inequality `σ_{i+j}(AB) ≤ σ_i(A) σ_j(B)`, with zero-indexed singular values
extended by zero, on arbitrary finite real matrix indices.
Horn–Johnson 1991, Theorem 3.3.16(d); empty dimensions and arbitrary indices are allowed, with no
dimension or rank side condition.
atlas: weyl-product-singular-values -/
theorem singularValues_mul_add_le {m p n : Type*}
    [Fintype m] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]
    (A : Matrix m p ℝ) (B : Matrix p n ℝ) (i j : ℕ) :
    singularValues (A * B) (i + j) ≤ singularValues A i * singularValues B j := by
  have h := singularValues_mul_add_le_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin p))
    (B.reindex (Fintype.equivFin p) (Fintype.equivFin n)) i j
  have hAB : A.reindex (Fintype.equivFin m) (Fintype.equivFin p) *
      B.reindex (Fintype.equivFin p) (Fintype.equivFin n) =
      (A * B).reindex (Fintype.equivFin m) (Fintype.equivFin n) := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rwa [hAB, singularValues_reindex, singularValues_reindex, singularValues_reindex] at h

end NLAlib

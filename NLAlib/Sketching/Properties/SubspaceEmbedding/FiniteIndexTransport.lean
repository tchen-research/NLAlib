import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Sketching.Properties.SubspaceEmbedding.SingularValueEmbedding
/-!
# Relabelling invariance of subspace embeddings

`isSubspaceEmbedding_reindex_iff`: relabelling sketch rows, ambient coordinates and frame
coefficients preserves `IsSubspaceEmbedding`. The singular-value criteria on arbitrary finite
indices are `specNorm_gram_sub_one_le_iff_singularValues_sq` and
`isSubspaceEmbedding_iff_singularValues` (`SingularValueEmbedding`). Atlas: `ose-def`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

/-- Relabelling sketch rows, ambient coordinates, and frame coefficients
preserves the library embedding property. Source: permutation invariance of
the Gram criterion; supports `ose-def` and finite-index sparse sampling. -/
theorem isSubspaceEmbedding_reindex_iff
    {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    {S : Matrix p m ℝ} {U : Matrix m n ℝ} (hU : HasOrthonormalCols U)
    (ep : p ≃ ρ) (em : m ≃ ι) (en : n ≃ κ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsSubspaceEmbedding (S.reindex ep em) (U.reindex em en) ε ↔
      IsSubspaceEmbedding S U ε := by
  classical
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le
      (hU.reindex em en) hε,
    isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε]
  have hprod : S.reindex ep em * U.reindex em en = (S * U).reindex ep en := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hprod, transpose_mul_self_sub_one_reindex, specNorm_reindex]

end NLAlib

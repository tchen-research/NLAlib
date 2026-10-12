import NLAlib.Sketching.Properties.SubspaceEmbedding.Gram
import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Norms.Reindex
/-!
# The singular-value form of a subspace embedding

Atlas: `ose-def`, `svd`. The finite list is indexed by the domain dimension
(`j : Fin (card n)`), so zero singular values of a wide matrix are included. Empty frames give
an empty list and the equivalence remains valid. Row and column indices are arbitrary finite
types; the `Fin` case is the base, transported by `singularValues_reindex`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The `Fin` base case of `specNorm_gram_sub_one_le_iff_singularValues_sq`. -/
private theorem specNorm_gram_sub_one_le_iff_singularValues_sq_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    specNorm (Aᵀ * A - 1) ≤ ε ↔
      ∀ j : Fin n, 1 - ε ≤ singularValues A j ^ 2 ∧ singularValues A j ^ 2 ≤ 1 + ε := by
  rw [specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one,
    pi_norm_le_iff_of_nonneg hε]
  apply forall_congr'
  intro j
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨hlo, hup⟩ <;> constructor <;> linarith

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

omit [Fintype n] in
/-- Equivalent labels preserve Gram error as an exact matrix identity.
Horn–Johnson §5.6; atlas `ose-def`, `svd`. -/
theorem transpose_mul_self_sub_one_reindex {q : Type*} [Fintype q] [DecidableEq q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    (A.reindex em en)ᵀ * (A.reindex em en) - 1 = (Aᵀ * A - 1).reindex en en := by
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  change (Aᵀ * A).submatrix en.symm en.symm - 1 =
    (Aᵀ * A).submatrix en.symm en.symm - (1 : Matrix n n ℝ).submatrix en.symm en.symm
  rw [Matrix.submatrix_one_equiv]

/-- A Gram error bound is equivalent to bounds on every sorted squared singular value:
`‖AᵀA − I‖ ≤ ε` iff `1 − ε ≤ σⱼ(A)² ≤ 1 + ε` for every domain index `j < card n` (zero singular
values of a wide matrix included). Arbitrary finite row and column indices. Atlas: `ose-def`,
`svd`. -/
theorem specNorm_gram_sub_one_le_iff_singularValues_sq (A : Matrix m n ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    specNorm (Aᵀ * A - 1) ≤ ε ↔ ∀ j : Fin (Fintype.card n),
      1 - ε ≤ singularValues A j ^ 2 ∧ singularValues A j ^ 2 ≤ 1 + ε := by
  classical
  have h := specNorm_gram_sub_one_le_iff_singularValues_sq_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) hε
  rwa [transpose_mul_self_sub_one_reindex, specNorm_reindex, singularValues_reindex] at h

/-- Complete singular-value OSE equivalence for `0 ≤ ε ≤ 1`: the sketch preserves the subspace
iff every domain singular value of `S U` lies in `[√(1−ε), √(1+ε)]`. Arbitrary finite index
types; includes empty dimensions. Atlas: `ose-def`, `svd`.
atlas: ose-def -/
theorem isSubspaceEmbedding_iff_singularValues
    {S : Matrix p m ℝ} {U : Matrix m n ℝ} (hU : HasOrthonormalCols U)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsSubspaceEmbedding S U ε ↔ ∀ j : Fin (Fintype.card n),
      Real.sqrt (1 - ε) ≤ singularValues (S * U) j ∧
        singularValues (S * U) j ≤ Real.sqrt (1 + ε) := by
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε,
    specNorm_gram_sub_one_le_iff_singularValues_sq (S * U) hε]
  apply forall_congr'
  intro j
  have hlo0 : 0 ≤ 1 - ε := by linarith
  have hup0 : 0 ≤ 1 + ε := by linarith
  have hlo := Real.sq_sqrt hlo0
  have hup := Real.sq_sqrt hup0
  have hs := singularValues_nonneg (S * U) j
  have hls := Real.sqrt_nonneg (1 - ε)
  have hus := Real.sqrt_nonneg (1 + ε)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

end NLAlib

import NLAlib.Matrix.FiniteIndexTransport
import NLAlib.Sketching.SingularValueEmbedding

/-!
# Singular-value embedding criteria on arbitrary finite indices

Atlas: `ose-def`, `svd`. The input sketch and frame use arbitrary finite
index types, including empty ones. The parent singular-value list currently
uses `Fin` indices; the criteria normalize explicitly to `Fin(card)` without
introducing a second singular-value definition.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

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

/-- The squared-singular-value Gram criterion for arbitrary finite row and
column indices. Atlas `ose-def`, `svd`. The singular-value list uses explicit
`Fin(card)` normalization; zero domain singular values remain included. -/
theorem specNorm_gram_sub_one_le_iff_singularValues_sq_fintype
    (A : Matrix m n ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    specNorm (Aᵀ * A - 1) ≤ ε ↔ ∀ j : Fin (Fintype.card n),
      1 - ε ≤ singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) j ^ 2 ∧
        singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) j ^ 2 ≤ 1 + ε := by
  have h := specNorm_gram_sub_one_le_iff_singularValues_sq
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) hε
  rwa [transpose_mul_self_sub_one_reindex, specNorm_reindex] at h

/-- Complete OSE singular-value criterion on arbitrary finite indices.
For `0 ≤ ε ≤ 1`, every domain singular value of the normalized `S U` lies in
`[√(1−ε), √(1+ε)]` precisely when `S` embeds the frame's subspace.
Atlas `ose-def`, `svd`; the list uses explicit `Fin(card)` normalization.
atlas: ose-def -/
theorem isSubspaceEmbedding_iff_singularValues_fintype
    {S : Matrix p m ℝ} {U : Matrix m n ℝ} (hU : HasOrthonormalCols U)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsSubspaceEmbedding S U ε ↔ ∀ j : Fin (Fintype.card n),
      Real.sqrt (1 - ε) ≤
        singularValues ((S * U).reindex (Fintype.equivFin p) (Fintype.equivFin n)) j ∧
      singularValues ((S * U).reindex (Fintype.equivFin p) (Fintype.equivFin n)) j ≤
        Real.sqrt (1 + ε) := by
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε,
    specNorm_gram_sub_one_le_iff_singularValues_sq_fintype (S * U) hε]
  apply forall_congr'
  intro j
  have hlo0 : 0 ≤ 1 - ε := by linarith
  have hup0 : 0 ≤ 1 + ε := by linarith
  have hlo := Real.sq_sqrt hlo0
  have hup := Real.sq_sqrt hup0
  have hs := singularValues_nonneg
    ((S * U).reindex (Fintype.equivFin p) (Fintype.equivFin n)) j
  have hls := Real.sqrt_nonneg (1 - ε)
  have hus := Real.sqrt_nonneg (1 + ε)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

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

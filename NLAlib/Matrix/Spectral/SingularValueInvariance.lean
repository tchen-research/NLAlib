import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Subspaces.Projections
/-!
# Invariances of singular values

`singularValues` (on arbitrary finite index types) is invariant under transposition, under
left multiplication by a column isometry `H` (`HᵀH = 1`, in particular an orthogonal matrix)
and under right multiplication by `Hᵀ` (in particular by an orthogonal matrix), at every
natural index including the padded zeros. Relabeling invariance is
`singularValues_reindex` (`SingularValueSpectrum.lean`).

Source: Horn–Johnson 2013, §2.6.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Transposition preserves the singular values of a `Fin`-indexed real matrix (base case of
`singularValues_transpose`, via the uniqueness of the SVD). -/
private theorem singularValues_transpose_fin {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    singularValues Aᵀ = singularValues A := by
  funext k
  by_cases hk : k < min b a
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    exact singularValues_eq_of_eq_mul_rectDiag_mul h.transpose_mul_right h.transpose_mul_left
      (singularValues_nonneg A) (singularValues_antitone A) h.transpose_eq hk
  · rw [singularValues_eq_zero_of_min_le _ (by simpa only [Fintype.card_fin] using not_lt.1 hk),
      singularValues_eq_zero_of_min_le _
        (by simp only [Fintype.card_fin]; rw [min_comm]; exact not_lt.1 hk)]

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- `σ(Aᵀ) = σ(A)`: transposition preserves every singular value, including the padded zeros
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_transpose [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    singularValues Aᵀ = singularValues A := by
  rw [← singularValues_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    ← singularValues_reindex Aᵀ (Fintype.equivFin n) (Fintype.equivFin m),
    ← Matrix.transpose_reindex, singularValues_transpose_fin]

/-- Left multiplication by a column isometry `H` (`HᵀH = 1`; e.g. a square orthogonal matrix)
preserves every singular value, including the padded zeros (Horn–Johnson 2013, §2.6): the
Gram matrices agree. Atlas `svd`. -/
theorem singularValues_isometry_mul [DecidableEq n] [DecidableEq p]
    {H : Matrix m p ℝ} (hH : HasOrthonormalCols H) (A : Matrix p n ℝ) :
    singularValues (H * A) = singularValues A := by
  funext k
  apply singularValues_eq_of_gram_eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Hᵀ H A, show Hᵀ * H = 1 from hH, Matrix.one_mul]

/-- Right multiplication by the transpose of a column isometry `H` (`HᵀH = 1`) preserves every
singular value, including the padded zeros (Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_mul_isometry_transpose [DecidableEq n] [DecidableEq p]
    {H : Matrix n p ℝ} (hH : HasOrthonormalCols H) (A : Matrix m p ℝ) :
    singularValues (A * Hᵀ) = singularValues A := by
  classical
  rw [← singularValues_transpose (A * Hᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
    singularValues_isometry_mul hH, singularValues_transpose]

/-- Right multiplication by an orthogonal matrix `V` (`VᵀV = 1`) preserves every singular
value, including the padded zeros (Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_mul_orthogonal [DecidableEq n] (A : Matrix m n ℝ)
    {V : Matrix n n ℝ} (hV : HasOrthonormalCols V) :
    singularValues (A * V) = singularValues A := by
  have hVt : HasOrthonormalCols Vᵀ := by
    rw [hasOrthonormalCols_iff_transpose_mul_self, Matrix.transpose_transpose]
    exact mul_eq_one_comm.1 hV
  simpa only [Matrix.transpose_transpose] using singularValues_mul_isometry_transpose hVt A

end NLAlib

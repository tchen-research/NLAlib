import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Subspaces.Projections
/-!
# Invariances of singular values

`singularValues` (over `ℝ` or `ℂ`, on arbitrary finite index types) is invariant under conjugate
transposition, under left multiplication by a matrix `H` with orthonormal columns
(`HᴴH = 1`, in particular a unitary matrix) and under right multiplication by `Hᴴ` (in
particular by a unitary matrix), at every natural index including the padded zeros. Relabeling
invariance is `singularValues_reindex` (`SingularValueSpectrum.lean`).

Source: Horn–Johnson 2013, §2.6 and §7.3.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- `σ(Aᴴ) = σ(A)`: conjugate transposition preserves every singular value, including the
padded zeros (Horn–Johnson 2013, §7.3). Atlas `svd`. -/
theorem singularValues_conjTranspose [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValues Aᴴ = singularValues A := by
  funext k
  by_cases hk : k < min (Fintype.card n) (Fintype.card m)
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    exact singularValues_eq_of_eq_mul_rectDiag_mul h.conjTranspose_mul_right
      h.conjTranspose_mul_left (singularValues_nonneg A) (singularValues_antitone A)
      h.conjTranspose_eq hk
  · rw [singularValues_eq_zero_of_min_le _ (not_lt.1 hk),
      singularValues_eq_zero_of_min_le _ (by rw [min_comm]; exact not_lt.1 hk)]

/-- `σ(Aᵀ) = σ(A)` for a real matrix (`Aᵀ = Aᴴ`). Horn–Johnson 2013, §7.3. Atlas `svd`. -/
theorem singularValues_transpose [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    singularValues Aᵀ = singularValues A := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact singularValues_conjTranspose A

/-- Left multiplication by a matrix `H` with orthonormal columns (`HᴴH = 1`; e.g. a unitary
matrix) preserves every singular value, including the padded zeros (Horn–Johnson 2013, §7.3):
the Gram matrices agree. Atlas `svd`. -/
theorem singularValues_isometry_mul [DecidableEq n] [DecidableEq p]
    {H : Matrix m p 𝕜} (hH : HasOrthonormalCols H) (A : Matrix p n 𝕜) :
    singularValues (H * A) = singularValues A := by
  funext k
  apply singularValues_eq_of_gram_eq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hᴴ H A,
    hH.conjTranspose_mul_self, Matrix.one_mul]

/-- Right multiplication by the conjugate transpose of a matrix `H` with orthonormal columns
(`HᴴH = 1`) preserves every singular value, including the padded zeros (Horn–Johnson 2013,
§7.3). Atlas `svd`. -/
theorem singularValues_mul_isometry_conjTranspose [DecidableEq m] [DecidableEq n] [DecidableEq p]
    {H : Matrix n p 𝕜} (hH : HasOrthonormalCols H) (A : Matrix m p 𝕜) :
    singularValues (A * Hᴴ) = singularValues A := by
  rw [← singularValues_conjTranspose (A * Hᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, singularValues_isometry_mul hH,
    singularValues_conjTranspose]

/-- Right multiplication by a unitary matrix `V` (`VᴴV = 1`) preserves every singular value,
including the padded zeros (Horn–Johnson 2013, §7.3). Atlas `svd`. -/
theorem singularValues_mul_unitary [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜)
    {V : Matrix n n 𝕜} (hV : HasOrthonormalCols V) :
    singularValues (A * V) = singularValues A := by
  have hVt : HasOrthonormalCols Vᴴ := by
    rw [hasOrthonormalCols_iff_conjTranspose_mul_self, Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 hV
  simpa only [Matrix.conjTranspose_conjTranspose] using
    singularValues_mul_isometry_conjTranspose hVt A

end NLAlib

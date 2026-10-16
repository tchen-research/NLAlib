import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Spectral.SpectralBounds

/-!
# Row, column, and entry blocks of rectangular coefficient families

These are ordinary finite matrices. Their Gram matrices are exactly the row,
column, and entry covariances used by linear matrix-series estimates and by
the finite-array recursion for matrix chaos.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {ι m n 𝕜 : Type*}

/-- Put a coefficient label next to the matrix column label. -/
def coefficientRow (A : ι → Matrix m n 𝕜) : Matrix m (ι × n) 𝕜 :=
  fun a jb => A jb.1 a jb.2

/-- Put a coefficient label next to the matrix row label. -/
def coefficientColumn (A : ι → Matrix m n 𝕜) : Matrix (ι × m) n 𝕜 :=
  fun ia b => A ia.1 ia.2 b

/-- Put each vectorized coefficient in a row. Both original matrix labels
are on the column side; no coordinate appears on both sides. -/
def coefficientEntryRows (A : ι → Matrix m n 𝕜) : Matrix ι (m × n) 𝕜 :=
  fun i ab => A i ab.1 ab.2

variable [Fintype ι] [Fintype m] [Fintype n] [RCLike 𝕜]

/-- The horizontal block Gram matrix is the sum of row variances. -/
theorem coefficientRow_mul_conjTranspose (A : ι → Matrix m n 𝕜) :
    coefficientRow A * (coefficientRow A)ᴴ = ∑ i, A i * (A i)ᴴ := by
  ext a b
  simp [coefficientRow, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]

/-- The vertical block Gram matrix is the sum of column variances. -/
theorem coefficientColumn_conjTranspose_mul (A : ι → Matrix m n 𝕜) :
    (coefficientColumn A)ᴴ * coefficientColumn A = ∑ i, (A i)ᴴ * A i := by
  ext a b
  simp [coefficientColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]

variable [DecidableEq ι] [DecidableEq m] [DecidableEq n]

/-- The horizontal block norm is the square root of the row-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_coefficientRow_sq (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientRow A) ^ 2 = specNorm (∑ i, A i * (A i)ᴴ) := by
  rw [← specNorm_mul_conjTranspose_self, coefficientRow_mul_conjTranspose]

/-- The vertical block norm is the square root of the column-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_coefficientColumn_sq (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientColumn A) ^ 2 = specNorm (∑ i, (A i)ᴴ * A i) := by
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, coefficientColumn_conjTranspose_mul]

/-- The row block norm equals the square root of the row-variance norm. -/
theorem specNorm_coefficientRow (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientRow A) = Real.sqrt (specNorm (∑ i, A i * (A i)ᴴ)) := by
  rw [← specNorm_coefficientRow_sq, Real.sqrt_sq (specNorm_nonneg _)]

/-- The column block norm equals the square root of the column-variance norm. -/
theorem specNorm_coefficientColumn (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientColumn A) = Real.sqrt (specNorm (∑ i, (A i)ᴴ * A i)) := by
  rw [← specNorm_coefficientColumn_sq, Real.sqrt_sq (specNorm_nonneg _)]

end NLAlib

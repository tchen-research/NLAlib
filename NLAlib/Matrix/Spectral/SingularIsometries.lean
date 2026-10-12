import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Spectral.SingularValueInvariance
/-!
# Singular values under rectangular isometries

Column isometries preserve every native singular value, with all padded zeros.
Horn–Johnson 2013, Section 2.6.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Left multiplication by a rectangular column isometry preserves every
singular value on arbitrary finite index types. Horn–Johnson 2013, Section 2.6. -/
theorem toEuclideanLin_singularValues_isometry_mul {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    {H : Matrix m p ℝ} (hH : HasOrthonormalCols H) (A : Matrix p n ℝ) (k : ℕ) :
    (H * A).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  apply toEuclideanLin_singularValues_eq_of_gram_eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Hᵀ H A, show Hᵀ * H = 1 from hH, Matrix.one_mul]

/-- Right multiplication by the transpose of a rectangular column isometry
preserves every singular value, including zero padding. Horn–Johnson 2013, Section 2.6. -/
theorem toEuclideanLin_singularValues_mul_isometry_transpose {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    {H : Matrix n p ℝ} (hH : HasOrthonormalCols H) (A : Matrix m p ℝ) (k : ℕ) :
    (A * Hᵀ).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  rw [← toEuclideanLin_singularValues_transpose (A * Hᵀ),
    Matrix.transpose_mul, Matrix.transpose_transpose,
    toEuclideanLin_singularValues_isometry_mul hH,
    toEuclideanLin_singularValues_transpose]

end NLAlib

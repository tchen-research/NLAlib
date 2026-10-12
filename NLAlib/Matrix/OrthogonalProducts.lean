import NLAlib.Matrix.Projections

/-!
# Products and transposes of orthonormal matrices

These immediate Gram identities are shared by canonical forms and Procrustes.
Horn–Johnson 2013, §2.1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A product of column isometries is a column isometry. Horn–Johnson §2.1. -/
theorem HasOrthonormalCols.mul {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p] {P : Matrix m n ℝ} {Q : Matrix n p ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) : HasOrthonormalCols (P * Q) := by
  change (P * Q)ᵀ * (P * Q) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P Q,
    hP, Matrix.one_mul, hQ]

/-- The transpose of a square orthogonal matrix is orthogonal, including
empty matrices. Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.transpose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℝ} (hU : HasOrthonormalCols U) : HasOrthonormalCols Uᵀ := by
  change Uᵀᵀ * Uᵀ = 1
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp hU

end NLAlib

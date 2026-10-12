import NLAlib.Matrix.Basic.MoorePenrose
import NLAlib.Matrix.Subspaces.Projections
import Mathlib.Tactic.FieldSimp

/-!
# Transformations of the Moore--Penrose inverse

Scalar multiplication, nonsingular square matrices, symmetric matrices and
left isometries. The identities hold at deficient and zero rank.
Source: Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def` and
`generalized-schur-complement-psd`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder
namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- Scaling the actual Moore--Penrose inverse by the inverse scalar.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def`, including rank zero. -/
theorem moorePenroseInverse_smul (c : ℝ) (A : Matrix m n ℝ) :
    moorePenroseInverse (c • A) = c⁻¹ • moorePenroseInverse A := by
  by_cases hc : c = 0
  · simp [hc]
  apply (isMoorePenroseInverse (c • A)).unique
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_moorePenroseInverse_mul]
    congr 1
    field_simp
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      moorePenroseInverse_mul_moorePenroseInverse]
    congr 1
    field_simp
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.transpose_smul, (mul_moorePenroseInverse_isSymm A).eq]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.transpose_smul, (moorePenroseInverse_mul_isSymm A).eq]

/-- On a nonsingular square matrix, the general inverse is the ordinary inverse.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def`. -/
theorem moorePenroseInverse_eq_inv_of_isUnit [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A) : moorePenroseInverse A = A⁻¹ := by
  apply (isMoorePenroseInverse A).unique
  have hDet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor <;> simp [Matrix.mul_nonsing_inv _ hDet, Matrix.nonsing_inv_mul _ hDet]

/-- The general inverse of a symmetric real matrix is symmetric.
Horn--Johnson 2013, Problem 7.3.P7; supports `generalized-schur-complement-psd`. -/
theorem moorePenroseInverse_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (moorePenroseInverse A).IsSymm := by
  show (moorePenroseInverse A).transpose = moorePenroseInverse A
  rw [← moorePenroseInverse_transpose, hA.eq]

/-- The general inverse of a left-isometric product is the reverse adjoint product.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def` for rectangular frames. -/
theorem moorePenroseInverse_mul_left_of_hasOrthonormalCols
    [DecidableEq n] [DecidableEq m] [DecidableEq p]
    (Q : Matrix p m ℝ) (A : Matrix m n ℝ) (hQ : HasOrthonormalCols Q) :
    moorePenroseInverse (Q * A) = moorePenroseInverse A * Qᵀ := by
  apply (isMoorePenroseInverse (Q * A)).unique
  have hQt : Qᵀ * Q = 1 := hQ
  constructor
  · calc
      Q * A * (moorePenroseInverse A * Qᵀ) * (Q * A) =
          Q * (A * moorePenroseInverse A * (Qᵀ * Q) * A) := by simp only [Matrix.mul_assoc]
      _ = Q * A := by rw [hQt, Matrix.mul_one, mul_moorePenroseInverse_mul]
  · calc
      moorePenroseInverse A * Qᵀ * (Q * A) * (moorePenroseInverse A * Qᵀ) =
          (moorePenroseInverse A * (Qᵀ * Q) * A * moorePenroseInverse A) * Qᵀ := by
            simp only [Matrix.mul_assoc]
      _ = moorePenroseInverse A * Qᵀ := by
        rw [hQt, Matrix.mul_one, moorePenroseInverse_mul_moorePenroseInverse]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Q * (moorePenroseInverse A)ᵀ * (Aᵀ * Qᵀ) =
          Q * (A * moorePenroseInverse A)ᵀ * Qᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Q * A * (moorePenroseInverse A * Qᵀ) := by
        rw [(mul_moorePenroseInverse_isSymm A).eq]
        simp only [Matrix.mul_assoc]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    have : (moorePenroseInverse A * Qᵀ) * (Q * A) = moorePenroseInverse A * A := by
      calc
        (moorePenroseInverse A * Qᵀ) * (Q * A) = moorePenroseInverse A * (Qᵀ * Q) * A := by
          simp only [Matrix.mul_assoc]
        _ = moorePenroseInverse A * A := by rw [hQt, Matrix.mul_one]
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
      congrArg Matrix.transpose this |>.trans (moorePenroseInverse_mul_isSymm A).eq |>.trans this.symm

/-- The actual Moore--Penrose inverse of a positive-semidefinite real matrix
is positive semidefinite, including singular matrices. Horn--Johnson,
Section 7.3; supports `generalized-schur-complement-psd`. -/
theorem moorePenroseInverse_posSemidef [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : (moorePenroseInverse A).PosSemidef := by
  have hB := moorePenroseInverse_isSymm (A := A) hA.isHermitian
  have h := hA.mul_mul_conjTranspose_same (moorePenroseInverse A)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq,
    moorePenroseInverse_mul_moorePenroseInverse] using h

end NLAlib

import NLAlib.Matrix.CholeskyDefinite

/-!
# First-pivot and trailing-block Cholesky identities

Nonnegative triangular factors have the advertised first square root. A
positive first pivot identifies the trailing factor with the Schur residual.
Source: Higham, Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
Supports `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

/-- The first entry of every nonnegative-diagonal lower-triangular Cholesky
factor is the nonnegative square root of the first matrix diagonal.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem cholesky_first_diag_eq_sqrt {n : ℕ}
    (A L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hLower : L.IsLowerTriangular) (hDiag : 0 ≤ L 0 0) (hFactor : L * Lᵀ = A) :
    L 0 0 = Real.sqrt (A 0 0) := by
  have hZero (i : Fin n) : L 0 i.succ = 0 := by
    have hLt : (0 : Fin (n + 1)) < i.succ := by
      simpa only [Fin.lt_def, Fin.val_zero, Fin.val_succ] using Nat.succ_pos i.val
    exact hLower hLt
  have h := congrFun (congrFun hFactor 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    hZero, zero_mul, Finset.sum_const_zero, add_zero] at h
  rw [← h, Real.sqrt_mul_self hDiag]

/-- First-column entries of a triangular factor are determined by the matrix
entries when the leading factor diagonal is positive. Higham, Theorem 10.1;
supports `cholesky-decomposition`. -/
theorem cholesky_first_col_eq_div {n : ℕ}
    (A L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hLower : L.IsLowerTriangular) (hDiag : 0 < L 0 0) (hFactor : L * Lᵀ = A)
    (i : Fin (n + 1)) : L i 0 = A i 0 / L 0 0 := by
  have hZero (j : Fin n) : L 0 j.succ = 0 := by
    have hLt : (0 : Fin (n + 1)) < j.succ := by
      simpa only [Fin.lt_def, Fin.val_zero, Fin.val_succ] using Nat.succ_pos j.val
    exact hLower hLt
  have h := congrFun (congrFun hFactor i) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    hZero, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact (eq_div_iff hDiag.ne').mpr h

/-- The trailing block of a positive-diagonal factor is the Cholesky factor
of the actual Schur residual. Higham, Theorem 10.1; supports
`cholesky-decomposition`. -/
theorem cholesky_trailing_mul_transpose {n : ℕ}
    (A L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hLower : L.IsLowerTriangular) (hDiag : 0 < L 0 0) (hFactor : L * Lᵀ = A) :
    L.submatrix Fin.succ Fin.succ * (L.submatrix Fin.succ Fin.succ)ᵀ =
      choleskyTrailingResidual A := by
  have hZero (j : Fin n) : L 0 j.succ = 0 := by
    have hLt : (0 : Fin (n + 1)) < j.succ := by
      simpa only [Fin.lt_def, Fin.val_zero, Fin.val_succ] using Nat.succ_pos j.val
    exact hLower hLt
  have hPivot := congrFun (congrFun hFactor 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    hZero, zero_mul, Finset.sum_const_zero, add_zero] at hPivot
  have hFirst (i : Fin n) : L i.succ 0 * L 0 0 = A i.succ 0 := by
    have h := congrFun (congrFun hFactor i.succ) 0
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      hZero, mul_zero, Finset.sum_const_zero, add_zero] using h
  have hRow (j : Fin n) : L 0 0 * L j.succ 0 = A 0 j.succ := by
    have h := congrFun (congrFun hFactor 0) j.succ
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      hZero, zero_mul, Finset.sum_const_zero, add_zero] using h
  have hCorrection (i j : Fin n) : A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ =
      L i.succ 0 * L j.succ 0 := by
    rw [← hPivot, ← hFirst i, ← hRow j]
    field_simp [hDiag.ne']
  ext i j
  have h := congrFun (congrFun hFactor i.succ) j.succ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix,
    choleskyTrailingResidual, hCorrection]
  change (∑ k : Fin n, L i.succ k.succ * L j.succ k.succ) =
    A i.succ j.succ - L i.succ 0 * L j.succ 0
  linarith

end NLAlib

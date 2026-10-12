import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Triangular products and orthogonal triangular matrices

The diagonal of a triangular product is the product of the diagonals. A real
lower-triangular orthogonal matrix with positive diagonal is the identity.
These elementary facts support uniqueness of positive-diagonal Cholesky and QR.
Source: Higham, Theorem 10.1; Trefethen--Bau, Theorems 7.1--7.2.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Diagonal multiplication for lower-triangular matrices.
Source: triangular matrix algebra; supports `cholesky-decomposition` and
`qr-decomposition`. -/
theorem mul_apply_diag_of_isLowerTriangular {n R : Type*} [Fintype n]
    [LinearOrder n] [Semiring R] (A B : Matrix n n R)
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hB (i := j) (j := i) hlt, mul_zero]
    · rw [hA (i := i) (j := j) hgt, zero_mul]
  · simp

/-- The ordinary inverse of a nonsingular lower-triangular real matrix remains
lower triangular. Source: triangular matrix algebra; supports Cholesky/QR. -/
theorem isLowerTriangular_inv_of_isUnit {n : Type*} [Fintype n] [LinearOrder n]
    {A : Matrix n n ℝ} (hA : A.IsLowerTriangular) (hUnit : IsUnit A) :
    A⁻¹.IsLowerTriangular := by
  let := Matrix.invertibleOfIsUnitDet A ((Matrix.isUnit_iff_isUnit_det A).mp hUnit)
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

/-- An orthogonal lower-triangular real matrix with positive diagonal is the
identity, including empty dimensions. Higham, Theorem 10.1; supports
`cholesky-decomposition` and `qr-decomposition`. -/
theorem eq_one_of_isLowerTriangular_of_mul_transpose_eq_one {n : Type*}
    [Fintype n] [LinearOrder n] {R : Matrix n n ℝ}
    (hR : R.IsLowerTriangular) (hOrth : R * Rᵀ = 1) (hDiag : ∀ i, 0 < R i i) : R = 1 := by
  have hOther : Rᵀ * R = 1 := mul_eq_one_comm.mp hOrth
  let : Invertible R := ⟨Rᵀ, hOther, hOrth⟩
  have hTranspose : Rᵀ.IsLowerTriangular := by
    have h := Matrix.blockTriangular_inv_of_blockTriangular hR
    rwa [Matrix.inv_eq_right_inv hOrth] at h
  have hOff (i j : n) (hij : i ≠ j) : R i j = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hR (i := i) (j := j) hlt
    · exact hTranspose (i := j) (j := i) hgt
  have hDiagonal (i : n) : R i i = 1 := by
    have h := congrFun (congrFun hOrth i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single i] at h
    · have hh := hDiag i
      nlinarith
    · intro j _ hji
      rw [hOff i j hji.symm, zero_mul]
    · simp
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.one_apply_eq] using hDiagonal i
  · rw [hOff i j hij, Matrix.one_apply_ne hij]

end NLAlib

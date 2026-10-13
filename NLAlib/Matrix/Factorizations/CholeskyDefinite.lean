import NLAlib.Matrix.Factorizations.Cholesky
import NLAlib.ForMathlib.LinearAlgebra.Matrix.Triangular
/-!
# Unique positive-diagonal Cholesky factorization

Positive definiteness makes every triangular factor invertible and its
nonnegative diagonal strictly positive; uniqueness is `IsCholesky.unique`. Source: Higham, Theorem 10.1;
Trefethen--Bau, Theorem 23.1. Supports `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- A square factor of a positive-definite Gram matrix is invertible.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem isUnit_of_mul_transpose_eq_posDef {A L : Matrix n n ℝ}
    (hA : A.PosDef) (hFactor : L * Lᵀ = A) : IsUnit L := by
  have hDet := congrArg Matrix.det hFactor
  rw [Matrix.det_mul, Matrix.det_transpose] at hDet
  have hNe : L.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hDet
    have hp := hA.det_pos
    linarith
  exact (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hNe)

/-- Every diagonal entry of an invertible lower-triangular real matrix is
nonzero; a nonnegative diagonal is therefore positive. Higham, Theorem 10.1;
supports `cholesky-decomposition`. -/
theorem diag_pos_of_isLowerTriangular_of_isUnit {L : Matrix n n ℝ}
    (hLower : L.IsLowerTriangular) (hUnit : IsUnit L) (hDiag : ∀ i, 0 ≤ L i i) :
    ∀ i, 0 < L i i := by
  have hDet : L.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det L).mp hUnit)
  rw [Matrix.det_of_isLowerTriangular L hLower] at hDet
  intro i
  have hNe : L i i ≠ 0 := (Finset.prod_ne_zero_iff.mp hDet) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hDiag i) hNe.symm

/-- Positive-definite real matrices have a unique positive-diagonal triangular
Cholesky factor, on every finite linearly ordered index type. Higham,
Theorem 10.1; Trefethen--Bau, Theorem 23.1.
atlas: cholesky-decomposition (partial) -/
theorem existsUnique_cholesky_of_posDef (A : Matrix n n ℝ) (hA : A.PosDef) :
    ∃! L : Matrix n n ℝ, L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = A := by
  obtain ⟨L, hLower, hDiag, hFactor'⟩ := exists_eq_mul_transpose_of_posSemidef hA.posSemidef
  have hFactor := hFactor'.symm
  have hPositive := diag_pos_of_isLowerTriangular_of_isUnit hLower
    (isUnit_of_mul_transpose_eq_posDef hA hFactor) hDiag
  refine ⟨L, ⟨hLower, hPositive, hFactor⟩, ?_⟩
  rintro M ⟨hMLower, hMPositive, hMFactor⟩
  exact IsCholesky.unique ⟨hMLower, hMPositive, hMFactor.symm⟩ ⟨hLower, hPositive, hFactor.symm⟩

/-- The determinant of a triangular Cholesky factorization is the product of
the squared factor diagonals, including an empty product; no positivity of the diagonal is
needed. Higham, Theorem 10.1; Trefethen–Bau 1997, Lect. 23; Golub–Van Loan 2013, §4.2.
atlas: cholesky-decomposition (partial) -/
theorem det_eq_prod_sq_diag_of_cholesky (A L : Matrix n n ℝ)
    (hLower : L.IsLowerTriangular) (hFactor : L * Lᵀ = A) : A.det = ∏ i, L i i ^ 2 := by
  rw [← hFactor, Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isLowerTriangular L hLower]
  simp only [sq, Finset.prod_mul_distrib]

end NLAlib

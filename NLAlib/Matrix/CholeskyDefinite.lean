import NLAlib.Matrix.CholeskySemidefinite
import NLAlib.ForMathlib.LinearAlgebra.Matrix.Triangular

/-!
# Unique positive-diagonal Cholesky factorization

Positive definiteness makes every triangular factor invertible and its
nonnegative diagonal strictly positive. The quotient of two such factors is
orthogonal and triangular, hence the identity. Source: Higham, Theorem 10.1;
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

/-- Positive-diagonal lower-triangular factors of the same positive-definite
matrix are equal, also in empty dimension. Higham, Theorem 10.1;
Trefethen--Bau, Theorem 23.1.
atlas: cholesky-decomposition (partial) -/
theorem cholesky_factor_unique {A L M : Matrix n n ℝ} (hA : A.PosDef)
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLDiag : ∀ i, 0 < L i i) (hMDiag : ∀ i, 0 < M i i)
    (hLFactor : L * Lᵀ = A) (hMFactor : M * Mᵀ = A) : L = M := by
  have hUnit := isUnit_of_mul_transpose_eq_posDef hA hLFactor
  have hDet := (Matrix.isUnit_iff_isUnit_det L).mp hUnit
  let R := L⁻¹ * M
  have hInvLower := isLowerTriangular_inv_of_isUnit hL hUnit
  have hLower : R.IsLowerTriangular := hInvLower.mul hM
  have hLR : L * R = M := by
    dsimp [R]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L hDet, Matrix.one_mul]
  have hOrth : R * Rᵀ = 1 := by
    calc
      R * Rᵀ = L⁻¹ * (M * Mᵀ) * (L⁻¹)ᵀ := by
        simp only [R, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = L⁻¹ * (L * Lᵀ) * (L⁻¹)ᵀ := by rw [hMFactor, ← hLFactor]
      _ = 1 := by
        rw [← Matrix.mul_assoc L⁻¹ L Lᵀ, Matrix.nonsing_inv_mul L hDet, Matrix.one_mul,
          ← Matrix.transpose_mul, Matrix.nonsing_inv_mul L hDet, Matrix.transpose_one]
  have hRDiag (i : n) : 0 < R i i := by
    have hd := congrFun (congrFun hLR i) i
    rw [mul_apply_diag_of_isLowerTriangular L R hL hLower i] at hd
    have hp : 0 < L i i * R i i := by rw [hd]; exact hMDiag i
    have hp' : 0 < R i i * L i i := by simpa only [mul_comm] using hp
    exact pos_of_mul_pos_left hp' (hLDiag i).le
  have hR := eq_one_of_isLowerTriangular_of_mul_transpose_eq_one hLower hOrth hRDiag
  rwa [hR, Matrix.mul_one] at hLR

/-- Positive-definite real matrices have a unique positive-diagonal triangular
Cholesky factor, on every finite linearly ordered index type. Higham,
Theorem 10.1; Trefethen--Bau, Theorem 23.1.
atlas: cholesky-decomposition (partial) -/
theorem existsUnique_cholesky_of_posDef (A : Matrix n n ℝ) (hA : A.PosDef) :
    ∃! L : Matrix n n ℝ, L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = A := by
  obtain ⟨L, hLower, hDiag, hFactor⟩ := exists_cholesky_of_posSemidef_fintype A hA.posSemidef
  have hPositive := diag_pos_of_isLowerTriangular_of_isUnit hLower
    (isUnit_of_mul_transpose_eq_posDef hA hFactor) hDiag
  refine ⟨L, ⟨hLower, hPositive, hFactor⟩, ?_⟩
  rintro M ⟨hMLower, hMPositive, hMFactor⟩
  exact cholesky_factor_unique hA hMLower hLower hMPositive hPositive hMFactor hFactor

/-- The determinant of a triangular Cholesky factorization is the product of
the squared factor diagonals, including an empty product. Higham, Theorem 10.1.
atlas: cholesky-decomposition (partial) -/
theorem det_eq_prod_sq_diag_of_cholesky (A L : Matrix n n ℝ)
    (hLower : L.IsLowerTriangular) (hFactor : L * Lᵀ = A) : A.det = ∏ i, L i i ^ 2 := by
  rw [← hFactor, Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isLowerTriangular L hLower]
  simp only [sq, Finset.prod_mul_distrib]

end NLAlib

import NLAlib.Matrix.PolynomialCalculus
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Principal minors and elementary spectral sums

The sum of fixed-order principal minors equals the corresponding elementary
sum of eigenvalues, by orthogonal diagonalization and Mathlib's determinant
coefficient identity. This is the normalizer identity of volume sampling.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Orthogonal diagonalization preserves the determinant polynomial `det(I+tG)`.
Source: manuscript `sa:volume`, the determinant coefficient argument. -/
theorem det_one_add_X_smul_eq_of_orthogonal_diagonalization
    {G U : Matrix n n ℝ} {d : n → ℝ} (hU : Uᵀ * U = 1)
    (hG : G = U * Matrix.diagonal d * Uᵀ) :
    Matrix.det (1 + (X : ℝ[X]) • G.map C) =
      Matrix.det (1 + (X : ℝ[X]) • (Matrix.diagonal d).map C) := by
  let Up : Matrix n n ℝ[X] := U.map C
  let Dp : Matrix n n ℝ[X] := (Matrix.diagonal d).map C
  have hp : Upᵀ * Up = 1 := by
    have h := congrArg (fun M : Matrix n n ℝ => M.map C) hU
    simpa [Up, Matrix.map_mul, Matrix.transpose_map, Matrix.map_one] using h
  have hp' : Up * Upᵀ = 1 := mul_eq_one_comm.1 hp
  have hg : G.map C = Up * Dp * Upᵀ := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have he : 1 + (X : ℝ[X]) • G.map C = Up * (1 + (X : ℝ[X]) • Dp) * Upᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hp']
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
  have hd : Up.det * Upᵀ.det = 1 := by
    rw [← Matrix.det_mul, hp', Matrix.det_one]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  dsimp only [Dp]
  calc Up.det * (1 + (X : ℝ[X]) • (Matrix.diagonal d).map C).det * Upᵀ.det =
      (Up.det * Upᵀ.det) * (1 + (X : ℝ[X]) • (Matrix.diagonal d).map C).det := by ring
    _ = _ := by rw [hd, one_mul]

/-- The sum of order-`k` principal minors equals the elementary symmetric sum of
the diagonal spectrum. Source: manuscript `sa:volume`, the normalizer identity;
Deshpande--Rademacher--Vempala--Wang (2006), volume-sampling proof. -/
theorem sum_det_principal_minors_eq_sum_prod_of_orthogonal_diagonalization
    {G U : Matrix n n ℝ} {d : n → ℝ} (hU : Uᵀ * U = 1)
    (hG : G = U * Matrix.diagonal d * Uᵀ) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, (G.submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)).det) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, d i := by
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    det_one_add_X_smul_eq_of_orthogonal_diagonalization hU hG,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro S _
  have hD : (Matrix.diagonal d).submatrix (Subtype.val : S → n) (Subtype.val : S → n) =
      Matrix.diagonal (fun i : S => d i) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply]
  rw [hD, Matrix.det_diagonal]
  exact Finset.prod_coe_sort S d

end NLAlib

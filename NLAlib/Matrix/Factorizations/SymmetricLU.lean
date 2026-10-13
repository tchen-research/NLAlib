import NLAlib.Matrix.Factorizations.LU

/-! # Symmetric LU as LDL transpose

A symmetric matrix's ordinary unit-lower LU factorization already supplies
its diagonal congruence. No second elimination algorithm is needed.
-/
noncomputable section
open scoped Matrix
open Matrix
namespace NLAlib

/-- A symmetric unit-lower LU factorization is the corresponding LDL transpose
factorization, with the actual upper factor's diagonal as pivots.
Source: matrix-toolkit derivations, Lemma “Symmetric LU needs no second elimination
algorithm”; Golub–Van Loan, §8.4.1. -/
theorem IsLU.eq_mul_diagonal_mul_transpose {n : Type*} [Fintype n] [LinearOrder n]
    {A L U : Matrix n n ℝ} (h : IsLU A L U) (hA : A.IsSymm) :
    A = L * diagonal (fun i => U i i) * Lᵀ := by
  have hL : IsUnit L.det := by rw [h.isUnitLowerTriangular.det_eq_one]; exact isUnit_one
  let B := L⁻¹ * A * (L⁻¹)ᵀ
  have hBu : B = U * (L⁻¹)ᵀ := by
    dsimp [B]
    rw [h.eq_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hL, Matrix.one_mul]
  have hBs : B.IsSymm := by
    change Bᵀ = B
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq]
    simp only [Matrix.mul_assoc]
  have hLt : ((L⁻¹)ᵀ).IsUpperTriangular :=
    isUpperTriangular_transpose_iff.mpr h.isUnitLowerTriangular.inv.isLowerTriangular
  have hBuT : B.IsUpperTriangular := by rw [hBu]; exact BlockTriangular.mul h.isUpperTriangular hLt
  have hBlT : B.IsLowerTriangular := by
    rw [← hBs.eq]
    exact isLowerTriangular_transpose_iff.mpr hBuT
  have hBd : B = diagonal (fun i => U i i) := by
    rw [eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hBlT hBuT]
    congr 1
    funext i
    rw [hBu, mul_apply_self_of_isUpperTriangular h.isUpperTriangular hLt]
    simp only [Matrix.transpose_apply, h.isUnitLowerTriangular.inv.apply_self, mul_one]
  have hback : L * B * Lᵀ = A := by
    dsimp [B]
    calc
      L * (L⁻¹ * A * (L⁻¹)ᵀ) * Lᵀ = (L * L⁻¹) * A * ((L⁻¹)ᵀ * Lᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv L hL,
        Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [hBd] at hback
  exact hback.symm

end NLAlib

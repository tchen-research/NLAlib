import NLAlib.Matrix.Factorizations.QR

/-!
# Similarity by a bordered orthogonal factor

Entrywise block identities for `diag(1, U)ᵀ B diag(1, U)`, used in the
concrete Householder Hessenberg recursion.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : ℕ}

/-- The trailing block of similarity by `diag(1,U)` is the similarity of the
trailing block. Source: finite block multiplication, Golub–Van Loan §1.3. -/
theorem submatrix_borderedUpper_transpose_mul_mul
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (U : Matrix (Fin n) (Fin n) ℝ) :
    ((borderedUpper (vecCons 1 0) U)ᵀ * B * borderedUpper (vecCons 1 0) U).submatrix
      Fin.succ Fin.succ = Uᵀ * B.submatrix Fin.succ Fin.succ * U := by
  have hU : (borderedUpper (vecCons 1 0) U)ᵀ = borderedUpper (vecCons 1 0) Uᵀ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      conjTranspose_borderedUpper_one U
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hU]

/-- The subdiagonal part of column zero transforms by `Uᵀ` under similarity by
`diag(1,U)`. Source: finite block multiplication, Golub–Van Loan §1.3. -/
theorem borderedUpper_transpose_mul_mul_succ_zero
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) :
    ((borderedUpper (vecCons 1 0) U)ᵀ * B * borderedUpper (vecCons 1 0) U) i.succ 0 =
      (Uᵀ *ᵥ fun j => B j.succ 0) i := by
  have hU : (borderedUpper (vecCons 1 0) U)ᵀ = borderedUpper (vecCons 1 0) Uᵀ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      conjTranspose_borderedUpper_one U
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    hU]

end NLAlib

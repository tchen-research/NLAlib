import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-! # Last-coordinate resolvent ratios

Deleting the final row and column gives the last diagonal cofactor. Its inverse entry
is the ratio of the leading characteristic polynomial to the full one. No tridiagonal
assumption is necessary for this identity; spectral applications require a nonzero
denominator rather than relying on the total inverse convention.
-/

noncomputable section
open Matrix Finset Polynomial
open scoped Matrix

namespace NLAlib

variable {q : ℕ}

/-- The last diagonal cofactor is the determinant of the leading block. -/
theorem adjugate_last_last_eq_det_leading (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) :
    J.adjugate (Fin.last q) (Fin.last q) = (J.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_apply, Matrix.det_succ_row _ (Fin.last q), sum_eq_single (Fin.last q)]
  · have hlead : (J.updateRow (Fin.last q) (Pi.single (Fin.last q) 1)).submatrix
        (Fin.last q).succAbove (Fin.last q).succAbove = J.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp
    rw [hlead]
    simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, mul_one]
    rw [show q + q = 2 * q by omega, pow_mul]
    simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The last inverse entry is the scalar cofactor ratio. The equality remains total
at a singular matrix, where both the nonsingular inverse and division use zero. -/
theorem inv_last_last_eq_det_leading_div_det (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) :
    J⁻¹ (Fin.last q) (Fin.last q) = (J.submatrix Fin.castSucc Fin.castSucc).det / J.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    adjugate_last_last_eq_det_leading, div_eq_mul_inv]
  exact mul_comm _ _

/-- The actual last-coordinate resolvent entry is the leading/full monic
characteristic-polynomial ratio. Source: focused reroutes, Section 3 (BL6).
atlas: gauss-radau-lobatto (partial) -/
theorem resolvent_last_last_eq_charpoly_leading_div_charpoly
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (z : ℝ) :
    (z • 1 - J)⁻¹ (Fin.last q) (Fin.last q) =
      (J.submatrix Fin.castSucc Fin.castSucc).charpoly.eval z / J.charpoly.eval z := by
  rw [inv_last_last_eq_det_leading_div_det, Matrix.eval_charpoly, Matrix.eval_charpoly]
  have heq : (z • (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) - J).submatrix
      Fin.castSucc Fin.castSucc = z • 1 - J.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [Matrix.one_apply]
  rw [heq]
  have hscalar {d : ℕ} : Matrix.scalar (Fin d) z = z • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hscalar, hscalar]

end NLAlib

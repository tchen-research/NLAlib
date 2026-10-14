import NLAlib.Matrix.Structured.RadauSchurBorders
import NLAlib.Matrix.Structured.JacobiBorderCharpoly

/-! # Explicit monic Radau corner ratios

The characteristic polynomial convention is `det(z I - J)`. Both endpoint Schur
corners therefore use the same minus sign in their last-coordinate resolvent ratio.
The left formula explicitly requires the endpoint shift to be invertible.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix

namespace NLAlib

/-- Negating an invertible real matrix negates its actual inverse. -/
theorem _root_.Matrix.inv_neg_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsUnit A) : (-A)⁻¹ = -A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul_neg]
  exact Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)

/-- Under the monic convention `χ(z)=det(z I-J)`, the actual left Schur corner
is `a-b² χ_leading(a)/χ(a)`. The inverse is used only at a nonsingular endpoint.
Source: focused mathematical reroutes, Section 3 (BL6).
atlas: gauss-radau-lobatto (partial) -/
theorem leftRadauCorner_single_last_eq_charpoly_ratio {q : ℕ}
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (b a : ℝ)
    (hJ : IsUnit (a • 1 - J)) :
    leftRadauCorner J (Pi.single (Fin.last q) b) a =
      a - b ^ 2 * (J.submatrix Fin.castSucc Fin.castSucc).charpoly.eval a / J.charpoly.eval a := by
  have hi : (J - a • 1)⁻¹ = -(a • 1 - J)⁻¹ := by
    rw [← neg_sub (a • 1) J, Matrix.inv_neg_of_isUnit hJ]
  rw [leftRadauCorner, hi, quadForm_single, Matrix.neg_apply,
    resolvent_last_last_eq_charpoly_leading_div_charpoly]
  ring

/-- The actual right Schur corner has the same monic minus-ratio convention.
Its spectral construction is used under a positive definite right endpoint shift.
Source: focused mathematical reroutes, Section 3 (BL6).
atlas: gauss-radau-lobatto (partial) -/
theorem rightRadauCorner_single_last_eq_charpoly_ratio {q : ℕ}
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (b c : ℝ) :
    rightRadauCorner J (Pi.single (Fin.last q) b) c =
      c - b ^ 2 * (J.submatrix Fin.castSucc Fin.castSucc).charpoly.eval c / J.charpoly.eval c := by
  rw [rightRadauCorner, quadForm_single, resolvent_last_last_eq_charpoly_leading_div_charpoly]
  ring

end NLAlib

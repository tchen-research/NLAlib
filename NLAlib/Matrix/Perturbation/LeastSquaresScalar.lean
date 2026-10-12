import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar conversion of least-squares perturbation estimates

These scalar inequalities convert the actual residual estimates into the
advertised relative and angle coefficients and an explicit quadratic
first-order remainder. Source: Higham, Theorem 20.1; Golub--Van Loan,
Theorem 5.3.1. Supports `least-squares-perturbation`.
-/

noncomputable section
namespace NLAlib

/-- The residual estimate implies Higham's advertised relative
least-squares forward coefficient; Higham, Theorem 20.1. -/
theorem least_squares_forward_ratio_le {Q M a X b R ε : ℝ}
    (hM : 0 < M) (hX : 0 < X) (ha : 0 ≤ a) (_hR : 0 ≤ R)
    (_hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : M * a * ε < 1)
    (hb : b ≤ M * X + R)
    (hQ : Q ≤ a / (1 - M * a * ε) *
      (ε * b + ε * M * X + a * ε * M * R)) :
    Q / X ≤ M * a * ε / (1 - M * a * ε) *
      (2 + (M * a + 1) * R / (M * X)) := by
  have hd : 0 < 1 - M * a * ε := sub_pos.mpr hsmall
  have hc : 0 ≤ a / (1 - M * a * ε) := div_nonneg ha hd.le
  calc
    Q / X ≤ (a / (1 - M * a * ε) *
      (ε * b + ε * M * X + a * ε * M * R)) / X :=
        div_le_div_of_nonneg_right hQ hX.le
    _ ≤ (a / (1 - M * a * ε) *
      (ε * (M * X + R) + ε * M * X + a * ε * M * R)) / X := by
        apply div_le_div_of_nonneg_right _ hX.le
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith [mul_le_mul_of_nonneg_left hb hε]
    _ = _ := by field_simp [hM.ne', hX.ne', hd.ne']; ring

/-- The same residual estimate yields the angle coefficient with the
actual fitted-vector length; Golub--Van Loan, Theorem 5.3.1. -/
theorem least_squares_forward_angle_coefficient_le {Q M a X b R ε L : ℝ}
    (hM : 0 < M) (hX : 0 < X) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hb : 0 < b) (hε : 0 ≤ ε) (hsmall : M * a * ε < 1)
    (hL : 0 < L) (hLX : L ≤ M * X) (hLb : L ≤ b)
    (hQ : Q ≤ a / (1 - M * a * ε) *
      (ε * b + ε * M * X + a * ε * M * R)) :
    Q / X ≤ ε * (2 * (M * a) / (L / b) + (M * a) ^ 2 * (R / L)) /
      (1 - M * a * ε) := by
  have hd : 0 < 1 - M * a * ε := sub_pos.mpr hsmall
  have hc : 0 ≤ a / (1 - M * a * ε) := div_nonneg ha hd.le
  have hbX : b / X ≤ M * b / L := by
    apply (div_le_div_iff₀ hX hL).2
    nlinarith [mul_le_mul_of_nonneg_left hLX hb.le]
  have hRX : R / X ≤ M * R / L := by
    apply (div_le_div_iff₀ hX hL).2
    nlinarith [mul_le_mul_of_nonneg_left hLX hR]
  have hMb : M ≤ M * b / L := by
    apply (le_div_iff₀ hL).2
    exact mul_le_mul_of_nonneg_left hLb hM.le
  calc
    Q / X ≤ (a / (1 - M * a * ε) *
      (ε * b + ε * M * X + a * ε * M * R)) / X :=
        div_le_div_of_nonneg_right hQ hX.le
    _ = a / (1 - M * a * ε) *
      (ε * (b / X) + ε * M + a * ε * M * (R / X)) := by
        field_simp [hX.ne', hd.ne']
    _ ≤ a / (1 - M * a * ε) *
      (ε * (M * b / L) + ε * (M * b / L) + a * ε * M * (M * R / L)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hbX hε)
          (mul_le_mul_of_nonneg_left hMb hε))
          (mul_le_mul_of_nonneg_left hRX (mul_nonneg (mul_nonneg ha hε) hM.le))
    _ = _ := by field_simp [hL.ne', hb.ne', hd.ne']; ring

/-- A half-size perturbation gives the explicit quadratic remainder
in the first-order least-squares coefficient; Golub--Van Loan, Theorem 5.3.1. -/
theorem first_order_reciprocal_bound_le {κ C ε : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (_hε : 0 ≤ ε) (hsmall : κ * ε ≤ 1 / 2) :
    ε * C / (1 - κ * ε) ≤ ε * C + 2 * κ * C * ε ^ 2 := by
  have hd : 0 < 1 - κ * ε := by linarith
  apply (div_le_iff₀ hd).2
  have hnonneg : 0 ≤ κ * C * ε ^ 2 * (1 - 2 * κ * ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg hκ hC) (sq_nonneg ε)) (by linarith)
  nlinarith [hnonneg]

end NLAlib

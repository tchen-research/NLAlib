import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Scalar logarithmic defect certificate

For the scalar capacity certificate we prove a quadratic upper bound on the
logarithmic defect `x - 1 - log x`: when the defect is at most `1 / 6`
(and `x > 0`), the square of `x - 1` is controlled by six times the defect.
The proof is elementary: at `y = sqrt x`, `log y ≤ y - 1` gives
`defect ≥ (sqrt x - 1)^2`; the bound on the defect then forces `x < 2`, so
`(sqrt x + 1)^2 ≤ 6`, and factoring `x - 1` gives the claim.
-/

noncomputable section

namespace Real

/-- The scalar logarithmic defect `x - 1 - log x` (with `x > 0`). -/
noncomputable def logDefect (x : ℝ) : ℝ :=
  x - 1 - Real.log x

/-- Scalar capacity certificate: for `0 < x`, if the logarithmic defect
`logDefect x` is at most `1 / 6`, then `(x - 1)^2 ≤ 6 * logDefect x`. -/
theorem sq_sub_one_le_six_mul_logDefect {x : ℝ} (hx : 0 < x)
    (hdef : logDefect x ≤ 1 / 6) :
    (x - 1) ^ 2 ≤ 6 * logDefect x := by
  have hs_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hs_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog_s : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs_pos
  have hlog_x : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc
      Real.log x = 2 * (Real.log x / 2) := by ring
      _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx.le]
  have hd_eq : logDefect x =
      (Real.sqrt x - 1) ^ 2 + 2 * ((Real.sqrt x - 1) - Real.log (Real.sqrt x)) := by
    unfold logDefect
    rw [hlog_x]
    nlinarith [hs_sq]
  have hd_ge : (Real.sqrt x - 1) ^ 2 ≤ logDefect x := by
    rw [hd_eq]
    nlinarith [hlog_s]
  have hd_nonneg : 0 ≤ logDefect x := (sq_nonneg (Real.sqrt x - 1)).trans hd_ge
  have hu_sq_le : (Real.sqrt x - 1) ^ 2 ≤ 1 / 6 := hd_ge.trans hdef
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfrac : 1 / 6 < (Real.sqrt 2 - 1) ^ 2 := by
    have hlt : Real.sqrt 2 < 17 / 12 := by
      have hsq : (Real.sqrt 2) ^ 2 < (17 / 12) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      have hlt' : |Real.sqrt 2| < |17 / 12| := sq_lt_sq.mp hsq
      simpa [abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_nonneg (by norm_num : 0 ≤ (17 / 12 : ℝ))] using hlt'
    have hsq : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [hsqrt2_sq]
    rw [hsq]
    linarith
  have hx_lt_two : x < 2 := by
    by_contra hnot
    have hge : 2 ≤ x := le_of_not_gt hnot
    have hs2 : Real.sqrt 2 ≤ Real.sqrt x := Real.sqrt_le_sqrt hge
    have h1le_s : 1 ≤ Real.sqrt x := Real.one_lt_sqrt_two.le.trans hs2
    have hsq_le : (Real.sqrt 2 - 1) ^ 2 ≤ (Real.sqrt x - 1) ^ 2 := by
      exact (sq_le_sq₀ (sub_nonneg.mpr Real.one_lt_sqrt_two.le) (sub_nonneg.mpr h1le_s)).2
        (sub_le_sub_right hs2 1)
    have hbad : 1 / 6 < (Real.sqrt x - 1) ^ 2 := hfrac.trans_le hsq_le
    linarith [hu_sq_le, hbad]
  have hsp6up : (Real.sqrt 2 + 1) ^ 2 ≤ 6 := by
    have hlt : Real.sqrt 2 < 3 / 2 := by
      have hsq : (Real.sqrt 2) ^ 2 < (3 / 2) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      have hlt' : |Real.sqrt 2| < |3 / 2| := sq_lt_sq.mp hsq
      simpa [abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ))] using hlt'
    have hsq : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      nlinarith [hsqrt2_sq]
    rw [hsq]
    linarith
  have hsp6 : (Real.sqrt x + 1) ^ 2 ≤ 6 := by
    have hs_lt : Real.sqrt x < Real.sqrt 2 := (Real.sqrt_lt_sqrt_iff hx.le).2 hx_lt_two
    have hlt : (Real.sqrt x + 1) ^ 2 < (Real.sqrt 2 + 1) ^ 2 := by
      nlinarith [hs_lt, hsqrt2_sq, hs_sq]
    exact le_of_lt (hlt.trans_le hsp6up)
  have hinner : (Real.sqrt x - 1) * (Real.sqrt x + 1) = x - 1 := by
    have h : (Real.sqrt x - 1) * (Real.sqrt x + 1) = (Real.sqrt x) ^ 2 - 1 := by ring
    rw [h, hs_sq]
  have hprod : (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 = (x - 1) ^ 2 := by
    rw [← mul_pow, hinner]
  calc
    (x - 1) ^ 2 = (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 := hprod.symm
    _ ≤ logDefect x * 6 := by
      exact mul_le_mul hd_ge hsp6 (sq_nonneg _) hd_nonneg
    _ = 6 * logDefect x := by ring

end Real

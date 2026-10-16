import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A common logarithmic budget for finite coefficient recursions

The product of all coefficient-array dimensions is unchanged when a chaos mode
is moved into a matrix coordinate. Its logarithm therefore bounds every linear
matrix-series dimension encountered by the recursion.
-/

namespace Real

/-- Four times a positive dimension product has logarithm greater than one. -/
theorem one_lt_log_four_mul {D : ℝ} (hD : 1 ≤ D) :
    1 < log (4 * D) := by
  apply (lt_log_iff_exp_lt (by positivity)).mpr
  linarith [exp_one_lt_three]

/-- A matrix with positive row and column dimensions uses no more logarithmic
budget than four times any upper bound on their product. -/
theorem log_two_mul_add_le_log_four_mul {r c D : ℝ}
    (hr : 1 ≤ r) (hc : 1 ≤ c) (hD : r * c ≤ D) :
    log (2 * (r + c)) ≤ log (4 * D) := by
  apply log_le_log (by positivity)
  have hrc : 1 ≤ r * c := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hc)]
  have hs : r + c ≤ 2 * r * c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hc)]
  nlinarith

/-- The coefficient-array product logarithm is bounded by a degree-dependent
multiple of the final `log(max(rows,cols)+coordinates)` expression. -/
theorem log_four_mul_mul_mul_pow_le {a b m : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 1 ≤ m) (q : ℕ) :
    log (4 * a * b * m ^ q) ≤ (q + 4 : ℝ) * log (max a b + m) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hm0 : 0 < m := by linarith
  have hd : 2 ≤ max a b + m := by linarith [le_max_left a b]
  have h2 : log 2 ≤ log (max a b + m) := log_le_log (by norm_num) hd
  have hla : log a ≤ log (max a b + m) := log_le_log ha0 (by
    linarith [le_max_left a b])
  have hlb : log b ≤ log (max a b + m) := log_le_log hb0 (by
    linarith [le_max_right a b])
  have hlm : log m ≤ log (max a b + m) := log_le_log hm0 (by
    linarith [le_max_left a b])
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    have h := log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [log_mul (by positivity) (pow_ne_zero q hm0.ne'),
    log_mul (by positivity) hb0.ne', log_mul (by norm_num) ha0.ne', log_pow, h4]
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith [mul_le_mul_of_nonneg_left hlm hq]

end Real

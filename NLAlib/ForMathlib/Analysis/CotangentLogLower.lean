import NLAlib.ForMathlib.Analysis.CotangentMidpoint
import NLAlib.ForMathlib.Analysis.CotangentOddCorrection

/-! # The sharp logarithmic central cotangent lower bound

The exact harmonic remainder and the odd correction preserve both the leading
coefficient and the additive constant of the universal interpolation lower bound.
-/
noncomputable section
open Real Set Finset
namespace NLAlib

/-- The universal logarithmic interpolation lower constant for one node is below one.
Source: focused reroutes, the degenerate one-node case; Mathlib's Euler-constant bound. -/
theorem logarithmic_interpolation_lower_one_lt_one :
    (2 / π) * (log (1 : ℝ) + eulerMascheroniConstant + log (4 / π)) < 1 := by
  have hp : 0 < π := pi_pos
  have hlog : log (4 / π) < 1 / 3 := by
    refine (log_le_sub_one_of_pos (by positivity : 0 < 4 / π)).trans_lt ?_
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]
    nlinarith [pi_gt_three]
  rw [log_one, zero_add, div_mul_eq_mul_div, div_lt_iff₀ hp]
  nlinarith [eulerMascheroniConstant_lt_two_thirds, pi_gt_three]

/-- The cotangent midpoint bound written with its exact logarithmic remainder.
Source: focused reroutes, equation `polyretry:midpoint-bound`. -/
theorem logarithmic_remainder_le_cotangent_sum {m N : ℕ} (hm : 0 < m) (hN : 0 < N)
    (hmN : 2 * m ≤ N) :
    (2 / π) * (log (N : ℝ) + eulerMascheroniConstant + log (4 / π)) +
      (2 / π) * (harmonicMidpointRemainder m + log (sin ((m : ℝ) * π / N))) ≤
        (2 / (N : ℝ)) * ∑ j ∈ range m, Real.cot (((j : ℝ) + 1 / 2) * π / N) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmNR : 2 * (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hh : 0 < π / (N : ℝ) := div_pos pi_pos hNR
  have hL : 0 < (m : ℝ) * π / N := by positivity
  have hLπ : (m : ℝ) * (π / N) ≤ π / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hNR]
    nlinarith [mul_le_mul_of_nonneg_left hmNR pi_pos.le]
  have hs : 0 < sin ((m : ℝ) * π / N) := sin_pos_of_pos_of_lt_pi hL (by
    have hLπ' : (m : ℝ) * π / N ≤ π / 2 := by simpa only [← mul_div_assoc] using hLπ
    linarith [pi_pos])
  have h := harmonic_add_log_sinc_le_mul_sum_cot_midpoint hm hh hLπ
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 / π by positivity)
  have hlogL : log ((m : ℝ) * π / N) = log (m : ℝ) + log π - log (N : ℝ) := by
    rw [log_div (mul_ne_zero hmR.ne' pi_pos.ne') hNR.ne', log_mul hmR.ne' pi_pos.ne']
  have hlog4 : log (4 / π) = 2 * log 2 - log π := by
    rw [log_div (by norm_num) pi_pos.ne', show (4 : ℝ) = 2 * 2 by norm_num,
      log_mul (by norm_num) (by norm_num)]
    ring
  have hlogR : log (sin ((m : ℝ) * π / N) / ((m : ℝ) * π / N)) =
      log (sin ((m : ℝ) * π / N)) - (log (m : ℝ) + log π - log (N : ℝ)) := by
    rw [log_div hs.ne' hL.ne', hlogL]
  have heqL : (2 / π) * (2 * (harmonic (2 * m) : ℝ) - (harmonic m : ℝ) +
      log (sin ((m : ℝ) * (π / N)) / ((m : ℝ) * (π / N)))) =
      (2 / π) * (log (N : ℝ) + eulerMascheroniConstant + log (4 / π)) +
      (2 / π) * (harmonicMidpointRemainder m + log (sin ((m : ℝ) * π / N))) := by
    simp only [← mul_div_assoc]
    rw [hlogR, hlog4]
    unfold harmonicMidpointRemainder
    ring
  rw [heqL] at hmul
  refine hmul.trans_eq ?_
  simp only [← mul_div_assoc]
  field_simp

/-- The odd central correction is strictly smaller than its harmonic remainder.
Source: focused reroutes, the exact odd-case correction estimate. -/
theorem neg_log_cos_sub_mul_tan_half_lt_harmonicMidpointRemainder {m : ℕ} (hm : 1 ≤ m) :
    -log (cos (π / (2 * (2 * (m : ℝ) + 1)))) -
      (π / (2 * (2 * (m : ℝ) + 1))) * tan (π / (4 * (2 * (m : ℝ) + 1))) <
        harmonicMidpointRemainder m := by
  let N := 2 * (m : ℝ) + 1
  let a := π / (2 * N)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : 3 ≤ N := by dsimp [N]; linarith
  have hN0 : 0 < N := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haπ : a ≤ π / 6 := by
    dsimp [a]
    apply div_le_div_of_nonneg_left pi_pos.le (by norm_num)
    linarith
  have hE := neg_log_cos_sub_mul_tan_half_le_quartic ha haπ
  have hpi4 : π ^ 4 < 256 := by
    have h := pow_lt_pow_left₀ pi_lt_four pi_pos.le (by decide : 4 ≠ 0)
    norm_num at h
    exact h
  have hquart : 2 * a ^ 4 / 27 < 1 / (6 * N ^ 2) := by
    have heq : 2 * a ^ 4 / 27 = π ^ 4 / (216 * N ^ 4) := by dsimp [a]; field_simp; ring
    rw [heq]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hN2 : 9 ≤ N ^ 2 := by nlinarith
    have hN4 : 0 < N ^ 2 := by positivity
    have hmul := mul_lt_mul_of_pos_right (show π ^ 4 < 36 * N ^ 2 by nlinarith) hN4
    have h6 := mul_lt_mul_of_pos_left hmul (by norm_num : (0 : ℝ) < 6)
    convert h6 using 1 <;> ring
  have hD := inv_sq_le_harmonicMidpointRemainder hm
  change 1 / (6 * N ^ 2) ≤ harmonicMidpointRemainder m at hD
  have harg : a / 2 = π / (4 * N) := by dsimp [a]; ring_nf
  rw [harg] at hE
  exact (hE.trans_lt hquart).trans_le hD

/-- The central cotangent sample, including its odd tangent correction, exceeds
the universal logarithmic constant for every number of nodes at least two.
Source: focused reroutes, equations `polyretry:central-cot` and `polyretry:midpoint-bound`.
This is a scalar helper; the interpolation sample identity is proved separately. -/
theorem logarithmic_lower_lt_central_cotangent_sum {N : ℕ} (hN : 2 ≤ N) :
    (2 / π) * (log (N : ℝ) + eulerMascheroniConstant + log (4 / π)) <
      (2 / (N : ℝ)) * ∑ j ∈ range (N / 2), Real.cot (((j : ℝ) + 1 / 2) * π / N) +
        (if Odd N then (1 / (N : ℝ)) * tan (π / (4 * N)) else 0) := by
  let m := N / 2
  have hm : 0 < m := by dsimp [m]; omega
  have hmN : 2 * m ≤ N := by dsimp [m]; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := logarithmic_remainder_le_cotangent_sum hm (show 0 < N by omega) hmN
  have hp : 0 < 2 / π := by positivity
  by_cases hNO : Odd N
  · have hNm : N = 2 * m + 1 := by
      have ho := Nat.odd_iff.mp hNO
      dsimp [m]
      omega
    have hNmR : (N : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hNm
    have harg : (m : ℝ) * π / N = π / 2 - π / (2 * N) := by rw [hNmR]; field_simp; ring
    rw [harg, sin_pi_div_two_sub] at h
    have hD := neg_log_cos_sub_mul_tan_half_lt_harmonicMidpointRemainder (show 1 ≤ m by omega)
    rw [← hNmR] at hD
    have hmul := mul_lt_mul_of_pos_left hD hp
    have hc : (2 / π) * ((π / (2 * (N : ℝ))) * tan (π / (4 * N))) =
        (1 / (N : ℝ)) * tan (π / (4 * N)) := by field_simp
    rw [mul_sub, hc] at hmul
    rw [if_pos hNO]
    dsimp [m] at h ⊢
    nlinarith
  · have hNE : Even N := Nat.not_odd_iff_even.mp hNO
    have hNm : N = 2 * m := by have he := Nat.even_iff.mp hNE; dsimp [m]; omega
    have hNmR : (N : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hNm
    have harg : (m : ℝ) * π / N = π / 2 := by rw [hNmR]; field_simp
    rw [harg, sin_pi_div_two, log_one, add_zero] at h
    have hD := inv_sq_le_harmonicMidpointRemainder (show 1 ≤ m by omega)
    have hDpos : 0 < harmonicMidpointRemainder m := (by positivity : 0 < 1 / (6 * (2 * (m : ℝ) + 1) ^ 2)).trans_le hD
    have hmul : 0 < (2 / π) * harmonicMidpointRemainder m := mul_pos hp hDpos
    rw [if_neg hNO, add_zero]
    dsimp [m] at h ⊢
    linarith

/-- The universal logarithmic interpolation lower constant for two nodes is below one.
Source: focused reroutes, the central cotangent sample at `N=2`. -/
theorem logarithmic_interpolation_lower_two_lt_one :
    (2 / π) * (log (2 : ℝ) + eulerMascheroniConstant + log (4 / π)) < 1 := by
  have h := logarithmic_lower_lt_central_cotangent_sum (N := 2) (by decide)
  have hc : Real.cot (π / 4) = 1 := by
    rw [Real.cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four, div_self (by positivity)]
  have hval : (2 / (2 : ℝ)) * (∑ j ∈ range (2 / 2), Real.cot (((j : ℝ) + 1 / 2) * π / 2)) +
      (if Odd (2 : ℕ) then (1 / (2 : ℝ)) * tan (π / (4 * 2)) else 0) = 1 := by
    have hno : ¬ Odd (2 : ℕ) := by decide
    norm_num only [Nat.reduceDiv, sum_range_one, Nat.cast_zero, zero_add, hno,
      if_false, add_zero, div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul]
    rw [show (1 / 2 : ℝ) * π / 2 = π / 4 by ring, hc]
  exact h.trans_eq hval

end NLAlib

import NLAlib.ForMathlib.Analysis.CotangentRemainder
import NLAlib.ForMathlib.Analysis.HarmonicRemainder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Exact midpoint cotangent lower bound

The regularized cotangent integral and its midpoint sum retain the harmonic
and logarithmic constants in the sharp Chebyshev-root sample estimate.
-/
noncomputable section
open Real Set Filter MeasureTheory Finset
open scoped Topology
namespace NLAlib

/-- The regularized cotangent integrates from its removable zero to `log(sin L/L)`.
Source: focused reroutes, the midpoint-concavity lower-bound calculation. -/
theorem integral_cot_sub_one_div_eq_log_sinc {L : ℝ} (hL : 0 < L) (hLπ : L ≤ π / 2) :
    (∫ x in 0..L, Real.cot x - 1 / x) = log (sin L / L) := by
  have hs (x : ℝ) (hx : x ∈ Icc 0 L) : sinc x ≠ 0 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      rw [sinc_of_ne_zero hx0]
      exact div_ne_zero (sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, pi_pos])).ne' hx0
  have hc : ContinuousOn (fun x : ℝ => log (sinc x)) (Icc 0 L) := continuous_sinc.continuousOn.log hs
  have hd (x : ℝ) (hx : x ∈ Ioo 0 L) :
      HasDerivAt (fun x : ℝ => log (sinc x)) (Real.cot x - 1 / x) x := by
    have hx0 : x ≠ 0 := hx.1.ne'
    have hs0 : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])).ne'
    have hdiv := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx0
    have h := hdiv.log (by dsimp only [Pi.div_apply, id_eq]; exact div_ne_zero hs0 hx0)
    have hder : HasDerivAt (fun x : ℝ => log (sin x / x)) (Real.cot x - 1 / x) x := by
      apply h.congr_deriv
      rw [Real.cot_eq_cos_div_sin]
      dsimp only [Pi.div_apply, id_eq]
      field_simp
    apply hder.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx.1] with y hy
    rw [sinc_of_ne_zero hy.ne']
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL.le hc hd
    ((continuousOn_cot_sub_one_div.mono (Icc_subset_Icc le_rfl hLπ)).intervalIntegrable_of_Icc hL.le)
  simpa only [sinc_zero, log_one, sub_zero, sinc_of_ne_zero hL.ne'] using hInt

/-- The reciprocal half-index sum is exactly `2H_(2m)−H_m`.
Source: focused reroutes, the finite odd-harmonic identity. -/
theorem sum_inv_nat_add_half (m : ℕ) :
    (∑ j ∈ range m, 1 / ((j : ℝ) + 1 / 2)) = 2 * (harmonic (2 * m) : ℝ) - (harmonic m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      harmonic_succ, harmonic_succ, harmonic_succ]
    push_cast
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have hm3 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
    have hmh : (m : ℝ) + 1 / 2 ≠ 0 := by positivity
    field_simp [hm, hm2, hm3, hmh]
    ring

/-- A finite midpoint cotangent sum has the exact harmonic-logarithmic lower bound.
Source: focused reroutes, equation `polyretry:midpoint-bound`. -/
theorem harmonic_add_log_sinc_le_mul_sum_cot_midpoint {m : ℕ} (hm : 0 < m)
    {h : ℝ} (hh : 0 < h) (hmh : (m : ℝ) * h ≤ π / 2) :
    2 * (harmonic (2 * m) : ℝ) - (harmonic m : ℝ) + log (sin ((m : ℝ) * h) / ((m : ℝ) * h)) ≤
      h * ∑ j ∈ range m, Real.cot (((j : ℝ) + 1 / 2) * h) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let g := fun x : ℝ => Real.cot x - 1 / x
  let a := fun j : ℕ => (j : ℝ) * h
  have hbounds (j : ℕ) (hj : j < m) : 0 ≤ a j ∧ a j ≤ a (j + 1) ∧ a (j + 1) ≤ π / 2 := by
    have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    dsimp [a]
    push_cast
    exact ⟨by positivity, by nlinarith, (mul_le_mul_of_nonneg_right hjR hh.le).trans hmh⟩
  have hgi (j : ℕ) (hj : j < m) : IntervalIntegrable g volume (a j) (a (j + 1)) := by
    obtain ⟨h0, hab, hb⟩ := hbounds j hj
    exact (continuousOn_cot_sub_one_div.mono (Icc_subset_Icc h0 hb)).intervalIntegrable_of_Icc hab
  have hmid (j : ℕ) (hj : j ∈ range m) :
      (∫ x in a j..a (j + 1), g x) ≤ h * g (((j : ℝ) + 1 / 2) * h) := by
    obtain ⟨h0, hab, hb⟩ := hbounds j (mem_range.mp hj)
    have hi := integral_cot_sub_one_div_le_mul_midpoint h0 hab hb
    have hd : a (j + 1) - a j = h := by dsimp [a]; push_cast; ring
    have hmida : (a j + a (j + 1)) / 2 = ((j : ℝ) + 1 / 2) * h := by dsimp [a]; push_cast; ring
    rw [hd, hmida] at hi
    exact hi
  have hs := sum_le_sum hmid
  rw [intervalIntegral.sum_integral_adjacent_intervals hgi, ← mul_sum] at hs
  simp only [a, Nat.cast_zero, zero_mul] at hs
  rw [integral_cot_sub_one_div_eq_log_sinc (mul_pos hmR hh) hmh] at hs
  have heq : h * (∑ j ∈ range m, g (((j : ℝ) + 1 / 2) * h)) =
      h * (∑ j ∈ range m, Real.cot (((j : ℝ) + 1 / 2) * h)) -
        (2 * (harmonic (2 * m) : ℝ) - (harmonic m : ℝ)) := by
    dsimp [g]
    rw [sum_sub_distrib, mul_sub, mul_sum, ← sum_inv_nat_add_half]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj0 : (j : ℝ) + 1 / 2 ≠ 0 := by positivity
    field_simp [hh.ne', hj0]
  rw [heq] at hs
  linarith

end NLAlib

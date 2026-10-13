import NLAlib.ForMathlib.Analysis.CotangentBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cotangent integral and midpoint bounds

Elementary convexity and integration of cotangent, used for the sharp Lobatto Lebesgue constant.
Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Real Set MeasureTheory

namespace NLAlib

/-- Cotangent is convex on the positive half quadrant.
Source: its nonnegative second derivative. -/
theorem convexOn_cot : ConvexOn ℝ (Ioc 0 (π / 2)) Real.cot := by
  have hs : ∀ x ∈ Ioc (0 : ℝ) (π / 2), 0 < sin x := by
    intro x hx
    exact sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt (by linarith [pi_pos]))
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => -1 / sin x ^ 2) (convex_Ioc 0 (π / 2))
    (fun x hx => (hasDerivAt_cot (hs x hx).ne').continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_cot (hs x (interior_subset hx)).ne').hasDerivWithinAt)
    (f'' := fun x => (2 * sin x * cos x) / (sin x ^ 2) ^ 2)
  · intro x hx
    have h := (hasDerivAt_const x (-1 : ℝ)).div ((Real.hasDerivAt_sin x).pow 2)
      (pow_ne_zero 2 (hs x (interior_subset hx)).ne')
    have hneg : HasDerivAt (fun x => -1 / sin x ^ 2) ((2 * sin x * cos x) / (sin x ^ 2) ^ 2) x := by
      exact h.congr_deriv (by simp only [Pi.pow_apply, zero_mul, neg_mul, sub_neg_eq_add, zero_add, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
    exact hneg.hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hs x hx').le)
      (cos_nonneg_of_mem_Icc ⟨by linarith [hx'.1, pi_pos], hx'.2⟩)) (sq_nonneg _)

/-- A continuous convex function has midpoint value no larger than its integral average.
Source: convexity paired at points reflected about the midpoint. -/
theorem mul_midpoint_le_integral_of_convexOn {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hc : ConvexOn ℝ (Icc a b) f) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := by
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hfr : ContinuousOn (fun x => f (a + b - x)) (Icc a b) :=
    hf.comp (continuous_const.sub continuous_id).continuousOn (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hfri : IntervalIntegrable (fun x => f (a + b - x)) volume a b := hfr.intervalIntegrable_of_Icc hab
  have hpoint : ∀ x ∈ Icc a b, f ((a + b) / 2) ≤ (f x + f (a + b - x)) / 2 := by
    intro x hx
    have hr : a + b - x ∈ Icc a b := by constructor <;> linarith [hx.1, hx.2]
    have h := hc.2 hx hr (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa only [smul_eq_mul, show (1 / 2 : ℝ) * x + 1 / 2 * (a + b - x) = (a + b) / 2 by ring,
      show (1 / 2 : ℝ) * f x + 1 / 2 * f (a + b - x) = (f x + f (a + b - x)) / 2 by ring] using h
  have hbound := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    ((hfi.add hfri).div_const 2) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_add hfi hfri, intervalIntegral.integral_comp_sub_left,
    show a + b - b = a by ring, show a + b - a = b by ring] at hbound
  simpa only [smul_eq_mul, add_self_div_two] using hbound

/-- The cotangent integral is the difference of log-sines, away from zero.
Source: the elementary fundamental theorem of calculus. -/
theorem integral_cot_eq_log_sin {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    (∫ x in a..b, Real.cot x) = log (sin b) - log (sin a) := by
  have hs : ∀ x ∈ Icc a b, 0 < sin x := by
    intro x hx
    exact sin_pos_of_pos_of_lt_pi (ha.trans_le hx.1) ((hx.2.trans hb).trans_lt (by linarith [pi_pos]))
  have hcot : ContinuousOn Real.cot (Icc a b) := fun x hx =>
    (hasDerivAt_cot (hs x hx).ne').continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcot.intervalIntegrable_of_Icc hab)
  intro x hx
  rw [uIcc_of_le hab] at hx
  have h := (Real.hasDerivAt_log (hs x hx).ne').comp x (Real.hasDerivAt_sin x)
  apply h.congr_deriv
  rw [Real.cot_eq_cos_div_sin]
  ring

/-- Cotangent is bounded by the reciprocal of its positive argument.
Source: `x ≤ tan x` on the positive half quadrant. -/
theorem cot_le_one_div {x : ℝ} (hx : 0 < x) (hxπ : x ≤ π / 2) : Real.cot x ≤ 1 / x := by
  by_cases heq : x = π / 2
  · simp only [heq, Real.cot_eq_cos_div_sin, cos_pi_div_two, sin_pi_div_two, zero_div, one_div_div]; positivity
  have hlt : x < π / 2 := lt_of_le_of_ne hxπ heq
  have hcos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
  have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith [pi_pos])
  have htan := Real.le_tan hx.le hlt
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos] at htan
  rw [Real.cot_eq_cos_div_sin, div_le_div_iff₀ hsin hx]
  simpa only [one_mul, mul_comm] using htan

end NLAlib

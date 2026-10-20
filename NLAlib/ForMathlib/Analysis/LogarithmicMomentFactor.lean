import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Dimension factors at logarithmic moment order

Reciprocal even powers of a nonnegative dimension are uniformly bounded
once the moment order dominates its logarithm. The zero dimension is included.
Source: the elementary logarithmic step in arXiv:2201.05142v3, Lemmas 7.3 and 7.5.
-/

noncomputable section
set_option autoImplicit false
namespace Real

/-- A reciprocal even power is at most `exp (1/2)` at logarithmic moment
order, including a zero base. -/
theorem rpow_inv_two_mul_le_exp_half_of_log_le {d p : ℝ}
    (hd : 0 ≤ d) (hp : 0 < p) (hlog : log d ≤ p) :
    d ^ (1/(2*p)) ≤ exp (1/2) := by
  rcases eq_or_lt_of_le hd with hzero | hpos
  · rw [← hzero, zero_rpow (by positivity : (1/(2*p) : ℝ) ≠ 0)]
    exact (exp_pos _).le
  · rw [rpow_def_of_pos hpos]
    apply exp_le_exp.mpr
    have hden : 0 < 2*p := by positivity
    have hh : log d/(2*p) ≤ 1/2 := (div_le_iff₀ hden).mpr (by linarith)
    simpa only [div_eq_mul_inv, one_mul] using hh

/-- Markov's exponential factor times a dimension factor at logarithmic
moment order is bounded by the explicit universal constant nine. -/
theorem exp_one_mul_rpow_inv_two_mul_le_nine_of_log_le {d p : ℝ}
    (hd : 0 ≤ d) (hp : 0 < p) (hlog : log d ≤ p) :
    exp 1 * d ^ (1/(2*p)) ≤ 9 := by
  have hdim := rpow_inv_two_mul_le_exp_half_of_log_le hd hp hlog
  have he : exp (1/2 : ℝ) ≤ exp 1 := exp_le_exp.mpr (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left (hdim.trans he) (exp_pos 1).le
  have hsq : exp 1 * exp 1 ≤ 9 := by
    have h := exp_one_lt_three
    nlinarith [exp_pos 1]
  exact hmul.trans hsq

end Real

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Scalar bounds for an exponential coordinate cutoff

At real exponent `p ≥ 2`, the head size `ceil (exp p)` has uniformly bounded
rank-to-Schatten loss, and its logarithmic position weight dominates `sqrt p`.
-/

noncomputable section
namespace Real

/-- An exponential head cutoff has a uniformly bounded low-rank Schatten
factor at every real exponent at least two. -/
theorem two_mul_two_mul_ceil_exp_rpow_le {p : ℝ} (hp : 2 ≤ p) :
    2 * (2 * (⌈exp p⌉₊ : ℝ)) ^ (1 / p) ≤ 32 := by
  have hp0 : 0 < p := by linarith
  have he : 1 ≤ exp p := one_le_exp_iff.mpr hp0.le
  have hceil : (⌈exp p⌉₊ : ℝ) ≤ 2 * exp p := by
    have h := Nat.ceil_lt_add_one (exp_pos p).le
    linarith
  have hpow : (2 * (⌈exp p⌉₊ : ℝ)) ^ (1 / p) ≤ (4 * exp p) ^ (1 / p) :=
    rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hfour : (4 : ℝ) ^ (1 / p) ≤ 4 := by
    apply (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      ((div_le_iff₀ hp0).mpr (by linarith : (1 : ℝ) ≤ 1 * p))).trans_eq
    exact rpow_one 4
  have hexp : exp p ^ (1 / p) = exp 1 := by
    rw [rpow_def_of_pos (exp_pos p), log_exp]
    congr 1
    field_simp
  rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (exp_pos p).le, hexp] at hpow
  have hexp4 : exp 1 ≤ 4 := by linarith [exp_one_lt_three]
  have hprod := mul_le_mul_of_nonneg_right hfour (exp_pos 1).le
  nlinarith

/-- The logarithm of the first position after the exponential cutoff is at
least the real exponent itself. -/
theorem le_log_ceil_exp_add_one (p : ℝ) : p ≤ log ((⌈exp p⌉₊ : ℝ) + 1) := by
  have h : exp p ≤ (⌈exp p⌉₊ : ℝ) + 1 := (Nat.le_ceil (exp p)).trans (by linarith)
  simpa only [log_exp] using log_le_log (exp_pos p) h

end Real

import NLAlib.Polynomial.BestApproximation.DoubleResolventPositivity
import NLAlib.Polynomial.BestApproximation.LaguerreProjectionTail
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Pole-free explicit reciprocal exponential denominators

The initial-interval smoothing bounds and the finite coefficient tail certificate
cover the entire half-line. Source: focused reciprocal reroute, Section 1.
-/

noncomputable section
open Polynomial Set
namespace NLAlib

private theorem resolvent_smoothing_coefficient_pos (r : ℕ) :
    0 < (4/3:ℝ)^(r+1) - (1/4:ℝ)^(r+1) := by
  have h : (1/4:ℝ)^(r+1) < (4/3:ℝ)^(r+1) :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-- The explicit denominator and its derivative are strictly positive beyond
the algebraic cutoff, by the finite positive derivative expression.
Source: focused reciprocal reroute, tail positivity.
atlas: exp-rational-halfline (partial) -/
theorem doubleResolventExponentialDenominator_pos_on_tail {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 4*(n:ℝ) ≤ x) :
    0 < (doubleResolventExponentialDenominator n).eval x ∧
      0 < (doubleResolventExponentialDenominator n).derivative.eval x := by
  have hnonneg (r : ℕ) :
      0 ≤ ((derivative : ℝ[X] → ℝ[X])^[r] (laguerreExponentialProjection n)).eval x :=
    iterate_derivative_laguerreExponentialProjection_eval_nonneg n r hx
  rw [doubleResolventExponentialDenominator_eq_sum, eval_smul, smul_eq_mul]
  constructor
  · rw [eval_finsetSum]
    apply mul_pos (by norm_num)
    have hterm (r : ℕ) : 0 ≤ (((4/3:ℝ)^(r+1)-(1/4:ℝ)^(r+1)) •
        (derivative : ℝ[X] → ℝ[X])^[r] (laguerreExponentialProjection n)).eval x := by
      rw [eval_smul, smul_eq_mul]
      exact mul_nonneg (resolvent_smoothing_coefficient_pos r).le (hnonneg r)
    have h0 : 0 < (((4/3:ℝ)^(0+1)-(1/4:ℝ)^(0+1)) •
        (derivative : ℝ[X] → ℝ[X])^[0] (laguerreExponentialProjection n)).eval x := by
      rw [eval_smul, smul_eq_mul, Function.iterate_zero_apply]
      exact mul_pos (resolvent_smoothing_coefficient_pos 0)
        (laguerreExponentialProjection_eval_pos n hx)
    exact h0.trans_le (Finset.single_le_sum (fun r _ => hterm r)
      (show 0 ∈ Finset.range (n+1) by simp))
  · rw [derivative_smul, map_sum, eval_smul, smul_eq_mul, eval_finsetSum]
    apply mul_pos (by norm_num)
    have hterm (r : ℕ) :
        0 ≤ (derivative (((4/3:ℝ)^(r+1)-(1/4:ℝ)^(r+1)) •
          (derivative : ℝ[X] → ℝ[X])^[r] (laguerreExponentialProjection n))).eval x := by
      rw [derivative_smul, eval_smul, smul_eq_mul]
      simpa only [Function.iterate_succ_apply'] using
        mul_nonneg (resolvent_smoothing_coefficient_pos r).le (hnonneg (r+1))
    have h0 :
        0 < (derivative (((4/3:ℝ)^(0+1)-(1/4:ℝ)^(0+1)) •
          (derivative : ℝ[X] → ℝ[X])^[0] (laguerreExponentialProjection n))).eval x := by
      rw [derivative_smul, Function.iterate_zero_apply, eval_smul, smul_eq_mul]
      exact mul_pos (resolvent_smoothing_coefficient_pos 0)
        (laguerreExponentialProjection_derivative_eval_pos hn hx)
    exact h0.trans_le (Finset.single_le_sum (fun r _ => hterm r)
      (show 0 ∈ Finset.range (n+1) by simp))

/-- The explicit denominator is strictly positive and has strictly positive
derivative everywhere on the half-line in every positive degree.
Source: focused reciprocal reroute, global positivity.
atlas: exp-rational-halfline (partial) -/
theorem doubleResolventExponentialDenominator_pos_halfLine {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 ≤ x) :
    0 < (doubleResolventExponentialDenominator n).eval x ∧
      0 < (doubleResolventExponentialDenominator n).derivative.eval x := by
  by_cases hn4 : n ≤ 4
  · exact doubleResolventExponentialDenominator_pos_small_degrees hn hn4 hx
  · by_cases hxn : x ≤ 4*(n:ℝ)
    · exact ⟨eval_doubleResolventExponentialDenominator_pos_of_le_four_mul hx hxn,
        derivative_doubleResolventExponentialDenominator_pos_of_le_four_mul (by omega) hx hxn⟩
    · exact doubleResolventExponentialDenominator_pos_on_tail hn (le_of_not_ge hxn)

/-- The explicit denominator is increasing throughout the entire half-line.
Source: focused reciprocal reroute, global monotonicity.
atlas: exp-rational-halfline (partial) -/
theorem doubleResolventExponentialDenominator_monotoneOn_halfLine {n : ℕ} (hn : 0 < n) :
    MonotoneOn (doubleResolventExponentialDenominator n).eval (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    (doubleResolventExponentialDenominator n).continuous.continuousOn
  · intro x _
    exact ((doubleResolventExponentialDenominator n).hasDerivAt x).hasDerivWithinAt
  · intro x hx
    exact (doubleResolventExponentialDenominator_pos_halfLine hn (interior_subset hx)).2.le

end NLAlib

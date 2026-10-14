import NLAlib.Polynomial.BestApproximation.DoubleResolventExponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Positivity of the explicit exponential denominator

The simultaneous smoothing estimates prove positivity on the initial interval.
Source: Section 1 of `four_focused_mathematical_reroutes.tex`.
-/

noncomputable section
open Polynomial
namespace NLAlib

private theorem smoothingDerivative_error_factor_lt_one (n : ℕ) (hn : 5 ≤ n) :
    4 * Real.sqrt (15/112) * (Real.exp 1 / 3)^n < 1 := by
  have he : Real.exp 1 / 3 ≤ (11/12 : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hpow := (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.exp 1 / 3) he n).trans
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 11/12)
      (by norm_num : (11/12:ℝ) ≤ 1) hn)
  have hs : (Real.sqrt (15/112))^2 = (15/112 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsmall : (4 * Real.sqrt (15/112) * (11/12:ℝ)^5)^2 < 1 := by
    rw [mul_pow, mul_pow, hs]
    norm_num
  have hfactor : 4 * Real.sqrt (15/112) * (11/12:ℝ)^5 < 1 := by
    nlinarith [sq_nonneg (4 * Real.sqrt (15/112) * (11/12:ℝ)^5)]
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_lt hfactor

private theorem smoothingValue_error_factor_lt_one (n : ℕ) :
    Real.sqrt (5/42) * (Real.exp 1 / 3)^n < 1 := by
  have hp : (Real.exp 1 / 3)^n ≤ 1 :=
    pow_le_one₀ (by positivity) (by have := Real.exp_one_lt_three; linarith)
  have hs : Real.sqrt (5/42) < 1 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/42)
    nlinarith [Real.sqrt_nonneg (5/42)]
  exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) hp).trans_lt hs

private theorem exp_quarter_le_exp_one_pow {n : ℕ} {x : ℝ} (hx : x ≤ 4*n) :
    Real.exp (x/4) ≤ (Real.exp 1)^n := by
  rw [← Real.exp_nat_mul, mul_one]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The explicit denominator is strictly positive before the algebraic tail
cutoff for every degree. The proof uses its actual value error.
Source: focused reciprocal reroute, positivity on `[0,4n]`.
atlas: exp-rational-halfline (partial) -/
theorem eval_doubleResolventExponentialDenominator_pos_of_le_four_mul
    {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (hxn : x ≤ 4*n) :
    0 < (doubleResolventExponentialDenominator n).eval x := by
  have h := abs_exp_quarter_sub_doubleResolventExponentialDenominator_le n hx
  have hfactor : Real.sqrt (5/42) / 3^n * Real.exp (x/4) < 1 := by
    calc
      _ ≤ Real.sqrt (5/42) / 3^n * (Real.exp 1)^n :=
        mul_le_mul_of_nonneg_left (exp_quarter_le_exp_one_pow hxn) (by positivity)
      _ = Real.sqrt (5/42) * (Real.exp 1 / 3)^n := by rw [div_pow]; ring
      _ < 1 := smoothingValue_error_factor_lt_one n
  have hexp : Real.exp (x/2) = Real.exp (x/4) * Real.exp (x/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at h
  have := mul_lt_mul_of_pos_right hfactor (Real.exp_pos (x/4))
  have habs := le_abs_self (Real.exp (x/4) -
    (doubleResolventExponentialDenominator n).eval x)
  nlinarith

/-- The four small positive degrees have the exact rational coefficients
displayed in the focused reciprocal reroute. -/
theorem doubleResolventExponentialDenominator_small_degrees :
    doubleResolventExponentialDenominator 1 = C (215/216) + C (60/216)*X ∧
    doubleResolventExponentialDenominator 2 =
      C (7745/7776) + C (1860/7776)*X + C (360/7776)*X^2 ∧
    doubleResolventExponentialDenominator 3 =
      C (280055/279936) + C (70620/279936)*X + C (6840/279936)*X^2 + C (1440/279936)*X^3 ∧
    doubleResolventExponentialDenominator 4 =
      C (10075985/10077696) + C (2513220/10077696)*X + C (341640/10077696)*X^2 +
        C (10080/10077696)*X^3 + C (4320/10077696)*X^4 := by
  simp only [doubleResolventExponentialDenominator_eq_sum]
  norm_num [laguerreExponentialProjection, laguerreExponentialCoefficient,
    Fin.sum_univ_succ, Finset.sum_range_succ, laguerrePolynomial,
    Function.iterate_succ_apply', laguerreRodriguesOperator_apply, derivative_sub,
    derivative_smul, derivative_X_pow, derivative_C, derivative_add,
    derivative_mul, derivative_X, derivative_one, smul_eq_C_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_neg, eval_pow, eval_C, eval_X,
      eval_one]
    ring

/-- The derivative of the explicit denominator is strictly positive before the
tail cutoff, for every degree at least five. The value and derivative estimates
are simultaneous, so this proves the claimed monotonicity locally.
Source: focused reciprocal reroute, positivity on `[0,4n]`.
atlas: exp-rational-halfline (partial) -/
theorem derivative_doubleResolventExponentialDenominator_pos_of_le_four_mul
    {n : ℕ} (hn : 5 ≤ n) {x : ℝ} (hx : 0 ≤ x) (hxn : x ≤ 4*n) :
    0 < (doubleResolventExponentialDenominator n).derivative.eval x := by
  have h := abs_exp_quarter_div_four_sub_derivative_doubleResolventExponentialDenominator_le n hx
  have hfactor : 4 * (Real.sqrt (15/112) / 3^n * Real.exp (x/4)) < 1 := by
    calc
      _ ≤ 4 * (Real.sqrt (15/112) / 3^n * (Real.exp 1)^n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (exp_quarter_le_exp_one_pow hxn) (by positivity))
          (by norm_num)
      _ = 4 * Real.sqrt (15/112) * (Real.exp 1 / 3)^n := by rw [div_pow]; ring
      _ < 1 := smoothingDerivative_error_factor_lt_one n hn
  have hexp : Real.exp (x/2) = Real.exp (x/4) * Real.exp (x/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at h
  have := mul_lt_mul_of_pos_right hfactor (Real.exp_pos (x/4))
  have habs := le_abs_self (Real.exp (x/4)/4 -
    (doubleResolventExponentialDenominator n).derivative.eval x)
  nlinarith

/-- Both the denominator and its derivative are positive on the entire half-line
for the four exceptional small degrees, by their exact rational coefficients.
Source: focused reciprocal reroute, small-degree table.
atlas: exp-rational-halfline (partial) -/
theorem doubleResolventExponentialDenominator_pos_small_degrees
    {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4) {x : ℝ} (hx : 0 ≤ x) :
    0 < (doubleResolventExponentialDenominator n).eval x ∧
      0 < (doubleResolventExponentialDenominator n).derivative.eval x := by
  obtain ⟨h1, h2, h3, h4⟩ := doubleResolventExponentialDenominator_small_degrees
  rcases (show n=1 ∨ n=2 ∨ n=3 ∨ n=4 by omega) with rfl | rfl | rfl | rfl
  all_goals
    first | rw [h1] | rw [h2] | rw [h3] | rw [h4]
    constructor
    · simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
      positivity
    · simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
        derivative_X_pow, zero_mul, mul_one, zero_add,
        eval_add, eval_mul, eval_C, eval_X, eval_pow]
      positivity

end NLAlib

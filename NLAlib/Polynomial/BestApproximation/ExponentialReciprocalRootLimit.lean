import NLAlib.Polynomial.BestApproximation.ExponentialRationalBounds
import NLAlib.ForMathlib.Analysis.Real.LogarithmicScale

/-!
# The exact reciprocal-exponential root limit

Finite upper and lower certificates for actual pole-free type-`(0,n)` rational
functions imply the limit `1/3`. No sharp type-`(n,n)` asymptotic is used.
Source: focused reciprocal reroute, Section 1 and retained appendix.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace NLAlib

/-- The actual half-line minimax error is strictly positive at every finite
order, by the finite lower certificate.
Source: reciprocal lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialMinimaxError_pos (n : ℕ) :
    0 < reciprocalExponentialMinimaxError n := by
  have ha := reciprocalExponentialLowerCutoff_gt_two n
  exact (div_pos zero_lt_one (by positivity)).trans_le
    (reciprocalExponentialMinimaxError_ge_geometric_lower_bound n)

private theorem tendsto_log_reciprocalExponentialLowerCutoff_div_nat :
    Tendsto (fun n : ℕ => Real.log (reciprocalExponentialLowerCutoff n)/(n:ℝ))
      atTop (𝓝 0) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  convert Real.tendsto_log_affine_nat_div_nat
    (show 0 < 4*Real.log 3 by positivity) (4*Real.log 3+Real.log 4) using 1
  funext n
  congr 2
  dsimp [reciprocalExponentialLowerCutoff]
  ring

/-- The logarithmic slope of the actual best error equals `−log 3`.
The polynomial prefactor in the lower bound disappears on the linear scale.
Source: focused reciprocal reroute, geometric sandwich.
atlas: exp-rational-halfline (partial) -/
theorem tendsto_log_reciprocalExponentialMinimaxError_div_nat :
    Tendsto (fun n => Real.log (reciprocalExponentialMinimaxError n)/(n:ℝ))
      atTop (𝓝 (-Real.log 3)) := by
  let L : ℕ → ℝ := fun n =>
    -(Real.log 6/(n:ℝ)+(1/2:ℝ)*(Real.log (reciprocalExponentialLowerCutoff n)/(n:ℝ))) -
      Real.log 3
  let U : ℕ → ℝ := fun n => Real.log (Real.sqrt (40/21))/(n:ℝ)-Real.log 3
  have hL : Tendsto L atTop (𝓝 (-Real.log 3)) := by
    simpa only [L, add_zero, mul_zero, neg_zero, zero_sub] using
      ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 6)).add
        (tendsto_log_reciprocalExponentialLowerCutoff_div_nat.const_mul (1/2:ℝ))).neg.sub_const
          (Real.log 3)
  have hU : Tendsto U atTop (𝓝 (-Real.log 3)) := by
    simpa only [U, zero_sub] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (Real.sqrt (40/21)))).sub_const
        (Real.log 3)
  have hlo : ∀ᶠ n : ℕ in atTop, L n ≤
      Real.log (reciprocalExponentialMinimaxError n)/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
    have ha : 0 < reciprocalExponentialLowerCutoff n :=
      (by norm_num : (0:ℝ) < 2).trans (reciprocalExponentialLowerCutoff_gt_two n)
    have h := Real.log_le_log (by positivity :
      0 < 1/(6*Real.sqrt (reciprocalExponentialLowerCutoff n)*3^n))
      (reciprocalExponentialMinimaxError_ge_geometric_lower_bound n)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_sqrt ha.le,
      Real.log_pow] at h
    have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    dsimp [L]
    convert! hdiv using 1
    field_simp
    ring
  have hhi : ∀ᶠ n : ℕ in atTop,
      Real.log (reciprocalExponentialMinimaxError n)/(n:ℝ) ≤ U n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
    have h := Real.log_le_log (reciprocalExponentialMinimaxError_pos n)
      (reciprocalExponentialMinimaxError_le_geometric_upper_bound n)
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h
    have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    dsimp [U]
    convert! hdiv using 1
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU hlo hhi

/-- The best pole-free real type-`(0,n)` rational approximation error for
`exp (−x)` on `x≥0` has exact `n`th-root limit `1/3`.
This endpoint uses actual canonical rational-function degree/pole constraints.
Source: focused reciprocal reroute, exact retained root limit.
atlas: exp-rational-halfline (partial) -/
theorem tendsto_rpow_reciprocalExponentialMinimaxError_inv_nat :
    Tendsto (fun n => (reciprocalExponentialMinimaxError n) ^ (1/(n:ℝ)))
      atTop (𝓝 (1/3:ℝ)) := by
  have h := Real.tendsto_rpow_inv_nat_of_log_div_tendsto reciprocalExponentialMinimaxError_pos
    tendsto_log_reciprocalExponentialMinimaxError_div_nat
  simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 3), one_div] using h

end NLAlib

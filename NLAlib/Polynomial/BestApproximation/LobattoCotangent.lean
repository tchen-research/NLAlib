import NLAlib.ForMathlib.Analysis.CotangentIntegral
import NLAlib.ForMathlib.Analysis.LogRationalBound
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The sharp finite cotangent sum

The finite midpoint-cotangent sum bounds the Lobatto interpolation norm.
Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Real Set Finset MeasureTheory

namespace NLAlib

/-- The finite cotangent upper bound for interpolation at Chebyshev extrema.
Source: focused rederivations, Theorem `thm:lobatto`.
atlas: lebesgue-constant-chebyshev (partial) -/
def lobattoCotangentConstant (n : ℕ) : ℝ :=
  (1 / n : ℝ) * ∑ j ∈ range n, Real.cot (((j : ℝ) + 1 / 2) * π / (2 * n))

private theorem sin_lobatto_step_lower {n : ℕ} (hn : 0 < n) :
    π / (2 * ((n : ℝ) + 1)) ≤ sin (π / (2 * n)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hp2 : π ^ 2 ≤ 10 := by nlinarith [pi_lt_d2, pi_pos]
  have hN2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnum : 0 ≤ 24 * (n : ℝ) ^ 2 - π ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hp2 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hidentity : π / (2 * n) - (π / (2 * n)) ^ 3 / 6 - π / (2 * ((n : ℝ) + 1)) =
      π * (24 * (n : ℝ) ^ 2 - π ^ 2 * ((n : ℝ) + 1)) /
        (48 * (n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    field_simp
    ring
  have hdiff : 0 ≤ π / (2 * n) - (π / (2 * n)) ^ 3 / 6 - π / (2 * ((n : ℝ) + 1)) := by
    rw [hidentity]
    exact div_nonneg (mul_nonneg pi_pos.le hnum) (by positivity)
  have hsin := sin_ge_sub_cube (x := π / (2 * n)) (by positivity)
  linarith

/-- Midpoint convexity bounds the finite Lobatto cotangent sum by the log-sine integral.
Source: focused rederivations, the integral comparison in `thm:lobatto`. -/
theorem lobattoCotangentConstant_le_log_sin {n : ℕ} (hn : 0 < n) :
    lobattoCotangentConstant n ≤ (2 / π) * (2 - log (sin (π / (2 * n)))) := by
  let h : ℝ := π / (2 * n)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < h := by dsimp [h]; positivity
  have hnh : (n : ℝ) * h = π / 2 := by dsimp [h]; field_simp
  have hhπ : h ≤ π / 2 := by nlinarith
  have hcont : ContinuousOn Real.cot (Icc h (π / 2)) := by
    intro x hx
    exact (hasDerivAt_cot (sin_pos_of_pos_of_lt_pi (hh.trans_le hx.1)
      (by linarith [hx.2, pi_pos])).ne').continuousAt.continuousWithinAt
  have hcell : ∀ j ∈ range (n - 1),
      h * Real.cot (((j : ℝ) + 1 + 1 / 2) * h) ≤
        ∫ x in ((j : ℝ) + 1) * h..((j : ℝ) + 2) * h, Real.cot x := by
    intro j hj
    have hjn : j + 2 ≤ n := by have := mem_range.mp hj; omega
    have hjn' : (j : ℝ) + 2 ≤ n := by exact_mod_cast hjn
    have hsubset : Icc (((j : ℝ) + 1) * h) (((j : ℝ) + 2) * h) ⊆ Ioc 0 (π / 2) := by
      intro x hx
      constructor
      · nlinarith [show (0 : ℝ) ≤ j by positivity, hx.1]
      · nlinarith [hx.2]
    have hcc : ConvexOn ℝ (Icc (((j : ℝ) + 1) * h) (((j : ℝ) + 2) * h)) Real.cot :=
      convexOn_cot.subset hsubset (convex_Icc _ _)
    have hc : ContinuousOn Real.cot (Icc (((j : ℝ) + 1) * h) (((j : ℝ) + 2) * h)) :=
      fun x hx => (hasDerivAt_cot (sin_pos_of_pos_of_lt_pi (hsubset hx).1
        (by linarith [(hsubset hx).2, pi_pos])).ne').continuousAt.continuousWithinAt
    convert mul_midpoint_le_integral_of_convexOn (by nlinarith :
      ((j : ℝ) + 1) * h ≤ ((j : ℝ) + 2) * h) hc hcc using 1; ring
  have hsum := sum_le_sum hcell
  have hintegral : ∑ j ∈ range (n - 1),
      ∫ x in ((j : ℝ) + 1) * h..((j : ℝ) + 2) * h, Real.cot x =
        ∫ x in h..π / 2, Real.cot x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => ((k : ℝ) + 1) * h) (f := Real.cot)
      (μ := volume) (n := n - 1) (by
        intro k hk
        apply hcont.intervalIntegrable_of_Icc hhπ |>.mono_set
        rw [uIcc_of_le hhπ]
        have hk' : (k : ℝ) + 2 ≤ n := by exact_mod_cast (show k + 2 ≤ n by omega)
        have hle : ((k : ℝ) + 1) * h ≤ ((k + 1 : ℕ) + 1 : ℝ) * h := by push_cast; nlinarith
        rw [uIcc_of_le hle]
        intro x hx
        constructor <;> push_cast at hx <;> nlinarith [show (0 : ℝ) ≤ k by positivity, hx.1, hx.2])
    have hnsub : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul, hnsub, hnh, show ∀ j : ℕ, (j : ℝ) + 1 + 1 = j + 2 by intro j; ring] using h
  simp only [← mul_sum] at hsum
  rw [hintegral, integral_cot_eq_log_sin hh hhπ le_rfl, sin_pi_div_two, log_one,
    zero_sub] at hsum
  have hfirst := cot_le_one_div (x := h / 2) (by linarith) (by linarith)
  have hfirst' : h * Real.cot (h / 2) ≤ 2 := by
    have hb := mul_le_mul_of_nonneg_left hfirst hh.le
    calc
      h * Real.cot (h / 2) ≤ h * (1 / (h / 2)) := hb
      _ = 2 := by field_simp
  have hsplit : (∑ j ∈ range n, Real.cot (((j : ℝ) + 1 / 2) * h)) =
      Real.cot (h / 2) + ∑ j ∈ range (n - 1), Real.cot (((j : ℝ) + 1 + 1 / 2) * h) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    rw [add_comm]
    congr 1
    congr 1
    ring
  have hscaled : h * ∑ j ∈ range n, Real.cot (((j : ℝ) + 1 / 2) * h) ≤ 2 - log (sin h) := by
    rw [hsplit, mul_add]
    linarith
  have hbound := mul_le_mul_of_nonneg_left hscaled (show 0 ≤ 2 / π by positivity)
  dsimp [lobattoCotangentConstant]
  have harg : ∀ j : ℕ, ((j : ℝ) + 1 / 2) * π / (2 * n) = ((j : ℝ) + 1 / 2) * h := by
    intro j; dsimp [h]; ring
  simp_rw [harg]
  have hfac : (1 / n : ℝ) = (2 / π) * h := by dsimp [h]; field_simp
  rw [hfac, mul_assoc]
  exact hbound

/-- The finite Lobatto cotangent sum has the sharp logarithmic coefficient `2/π`.
Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
atlas: lebesgue-constant-chebyshev (partial) -/
theorem lobattoCotangentConstant_le_log {n : ℕ} (hn : 0 < n) :
    lobattoCotangentConstant n ≤ 1 + (2 / π) * log ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hslo := sin_lobatto_step_lower hn
  have hpdiv : 0 < π / (2 * ((n : ℝ) + 1)) := by positivity
  have hlog := Real.log_le_log hpdiv hslo
  have hlogeq : log (π / (2 * ((n : ℝ) + 1))) = -log (2 / π) - log ((n : ℝ) + 1) := by
    rw [show π / (2 * ((n : ℝ) + 1)) = (2 / π)⁻¹ / ((n : ℝ) + 1) by field_simp,
      log_div (by positivity) (by positivity), log_inv]
  rw [hlogeq] at hlog
  calc
    lobattoCotangentConstant n ≤ (2 / π) * (2 - log (sin (π / (2 * n)))) :=
      lobattoCotangentConstant_le_log_sin hn
    _ ≤ (2 / π) * (2 + log (2 / π)) + (2 / π) * log ((n : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 / π by positivity)
      linarith
    _ ≤ 1 + (2 / π) * log ((n : ℝ) + 1) := by linarith [cotangent_log_remainder_le_one]

end NLAlib

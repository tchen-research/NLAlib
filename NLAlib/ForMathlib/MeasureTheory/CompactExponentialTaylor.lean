import NLAlib.ForMathlib.MeasureTheory.CompactExponential
import NLAlib.ForMathlib.Analysis.Calculus.SecondOrderIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Taylor comparisons for positive exponential representations

A positive compactly supported exponential representation gives the exact
second-order upper Taylor bound and a symmetric second-order lower bound.
The latter removes odd terms before integration against a symmetric law.
These are the deterministic BMV inputs in Tropp (2026), Section 4.
-/

noncomputable section

open MeasureTheory Set

namespace NLAlib

private theorem two_add_sq_le_exp_add_exp_neg (x : ℝ) :
    2 + x ^ 2 ≤ Real.exp x + Real.exp (-x) := by
  have hs := (Real.hasSum_cosh x).summable
  have h := hs.sum_le_tsum (Finset.range 2) (fun n _ =>
    div_nonneg ((even_two_mul n).pow_nonneg x) (Nat.cast_nonneg _))
  rw [← Real.cosh_eq_tsum] at h
  norm_num [Finset.sum_range_succ, Real.cosh_eq] at h
  linarith

namespace IsCompactExpRepresentation

variable {ν : FiniteMeasure ℝ} {F : ℝ → ℝ} {a b : ℝ}

/-- Positive compact exponential transforms are smooth, in every finite or
infinite differentiability order. -/
theorem contDiff (h : IsCompactExpRepresentation ν F a b) (k : WithTop ℕ∞) :
    ContDiff ℝ k F :=
  (show AnalyticOnNhd ℝ F univ from fun t _ => h.analyticAt t).contDiff

/-- An upper support bound controls the exact second-order Taylor remainder.
The coefficient remains defined at a zero upper support endpoint.
Source: Tropp (2026), BMV one-summand replacement argument. -/
theorem le_add_deriv_add_iteratedDeriv_two_mul_coefficient
    (h : IsCompactExpRepresentation ν F a b) :
    F 1 ≤ F 0 + deriv F 0 +
      iteratedDeriv 2 F 0 * expSecondRemainderCoefficient b := by
  apply le_add_deriv_add_mul_expSecondRemainderCoefficient (h.contDiff 2)
  intro t ht
  simpa using h.iteratedDeriv_even_le_exp_mul_zero 1 ht.1

/-- Symmetrizing a positive exponential transform gives its exact quadratic
Taylor lower bound, with all odd terms removed before any expectation.
Source: Tropp (2026), Gaussian one-summand lower comparison. -/
theorem two_mul_zero_add_iteratedDeriv_two_le_add
    (h : IsCompactExpRepresentation ν F a b) :
    2 * F 0 + iteratedDeriv 2 F 0 ≤ F 1 + F (-1) := by
  rw [← h.integral_exp 0, ← h.integral_exp 1, ← h.integral_exp (-1),
    h.iteratedDeriv_eq_integral]
  simp only [zero_mul, Real.exp_zero, mul_one, one_mul, neg_one_mul]
  have hpow : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) := by
    simpa using h.integrable_pow_mul_exp 2 0
  have hexp : Integrable Real.exp (ν : Measure ℝ) := by simpa using h.integrable_exp 1
  have hneg : Integrable (fun x : ℝ => Real.exp (-x)) (ν : Measure ℝ) := by
    simpa using h.integrable_exp (-1)
  rw [← integral_const_mul]
  simp only [mul_one]
  rw [← integral_add (integrable_const (2 : ℝ)) hpow, ← integral_add hexp hneg]
  exact integral_mono ((integrable_const (2 : ℝ)).add hpow)
    (hexp.add hneg)
    (fun x => two_add_sq_le_exp_add_exp_neg x)

end IsCompactExpRepresentation
end NLAlib

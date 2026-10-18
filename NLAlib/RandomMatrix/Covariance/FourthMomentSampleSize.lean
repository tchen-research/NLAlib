import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The fourth-moment covariance sample-size constant

The scalar arithmetic in Tropp (2026), Theorem 3.3 and Section 3.3.1. The
three error terms are controlled with the explicit rational split
`53/78 + 24/78 + 1/78 = 1`; no asymptotic or unspecified constant is used.
This file does not by itself assert a probability or matrix comparison.
-/

noncomputable section

namespace NLAlib

/-- The sample size with constant 26 controls all three error terms in the
fourth-moment covariance argument. Source: Tropp (2026), Section 3.3.1.
The squared fourth-moment parameter is written as `v`.
atlas: sample-covariance-fourth-moment-lower (partial) -/
theorem sqrt_add_sqrt_add_div_le_of_sample_size
    {v d s n ε : ℝ} (hv : 1 ≤ v) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hn : 0 < n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 26 * v * max d s / ε ^ 2 ≤ n) :
    Real.sqrt (12 * v * d / n) +
      Real.sqrt (2 * s * (v + Real.sqrt (12 * v * d / n) / 3) / n) +
      s / (3 * n) ≤ ε := by
  have hv0 : 0 ≤ v := by linarith
  have hsample : 26 * v * max d s ≤ n * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize
  have hsampled : 26 * v * d ≤ n * ε ^ 2 :=
    (mul_le_mul_of_nonneg_left (le_max_left d s) (by positivity)).trans hsample
  have hsamples : 26 * v * s ≤ n * ε ^ 2 :=
    (mul_le_mul_of_nonneg_left (le_max_right d s) (by positivity)).trans hsample
  let a := Real.sqrt (12 * v * d / n)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 12 * v * d / n := Real.sq_sqrt (by positivity)
  have ha : a ≤ 53 * ε / 78 := by
    have hb : 12 * v * d / n ≤ (53 * ε / 78) ^ 2 := by
      apply (div_le_iff₀ hn).mpr
      nlinarith
    nlinarith
  have ha1 : a ≤ 53 / 78 := by nlinarith
  have hab : v + a / 3 ≤ (287 / 234) * v := by nlinarith
  have hsab := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * s by positivity)
  have hbrad : 2 * s * (v + a / 3) / n ≤ (24 * ε / 78) ^ 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hb : Real.sqrt (2 * s * (v + a / 3) / n) ≤ 24 * ε / 78 := by
    have hbsq := Real.sq_sqrt (show 0 ≤ 2 * s * (v + a / 3) / n by positivity)
    have hb0 := Real.sqrt_nonneg (2 * s * (v + a / 3) / n)
    nlinarith
  have hc : s / (3 * n) ≤ ε / 78 := by
    apply (div_le_iff₀ (show 0 < 3 * n by positivity)).mpr
    have hvs : s ≤ v * s := by nlinarith
    have heps : ε ^ 2 ≤ ε := by nlinarith
    have hneps := mul_le_mul_of_nonneg_left heps hn.le
    nlinarith
  change a + Real.sqrt (2 * s * (v + a / 3) / n) + s / (3 * n) ≤ ε
  linarith

end NLAlib

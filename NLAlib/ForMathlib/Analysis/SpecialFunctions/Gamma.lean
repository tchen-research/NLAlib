import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gamma-function facts

* `Gamma_add_half_le_mul_sqrt`: `Γ(x + 1/2) ≤ Γ(x) √x` (log-convexity, Bohr–Mollerup);
* `lintegral_ofReal_mul_rpow_mul_exp_Ioi`: Euler's integral in `lintegral` form;
* `lintegral_rpow_mul_exp_le`: the truncated Gamma integral `∫₀ᵗ x^a e^{-x/2} ≤ t^{a+1}/(a+1)`.

Candidates for `Mathlib/Analysis/SpecialFunctions/Gamma/*`. Moved from
`NLAlib.Probability.ChiSquare.ChiSquare` and `NLAlib.Probability.Concentration.Basic.TailIntegral`
(dedup round, 2026-10-12).
-/

open MeasureTheory Real Set

namespace NLAlib

/-- `Γ(x + 1/2) ≤ Γ(x) √x` for `x > 0` (log-convexity of `Γ`, Bohr–Mollerup).
Atlas: `chi-square-neg-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.inv_chi_square_Lq_bound` (`icl_Gamma_add_half_le`). -/
theorem Gamma_add_half_le_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Gamma (x + 1 / 2) ≤ Gamma x * √x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG : 0 < Gamma x := Gamma_pos_of_pos hx
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne',
    ← Real.mul_rpow hG.le (by positivity), ← Real.sqrt_eq_rpow,
    show Gamma x * (x * Gamma x) = Gamma x ^ 2 * x by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le] at h
  exact h

/-- **Euler's integral in `lintegral` form**: `∫₀^∞ c t^{a-1} e^{-rt} dt = c (1/r)^a Γ(a)` for
`a, r > 0` and `c ≥ 0`. Atlas: `chi-square-neg-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.chi_square_neg_moment` (`cnm_gamma_lintegral`). -/
theorem lintegral_ofReal_mul_rpow_mul_exp_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (c : ℝ)
    (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * (t ^ (a - 1) * Real.exp (-(r * t))))
      = ENNReal.ofReal (c * ((1 / r) ^ a * Gamma a)) := by
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have hpos : 0 < (1 / r) ^ a * Gamma a := by
    have : 0 < Gamma a := Gamma_pos_of_pos ha
    positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hI]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c), integral_const_mul, hI]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
  positivity

/-- **Truncated Gamma integral bound.** For `a > -1` and `t ≥ 0`,
`∫₀ᵗ x^a e^{-x/2} dx ≤ t^{a+1} / (a + 1)` (drop the exponential factor).

Elementary; used for the chi-square small-ball density bound (Davidson–Szarek 2001,
Vershynin 2012). Atlas: `tail-integral`. Ported from Prove2me solution
`GaussianMatrix.integral_power_exp_le`.
atlas: tail-integral (partial) -/
theorem lintegral_rpow_mul_exp_le {a : ℝ} (ha : -1 < a) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 t) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) ha)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 this
  calc ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ∫⁻ x in Ioc 0 t, ENNReal.ofReal (x ^ a) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        apply ENNReal.ofReal_le_ofReal
        have h1 : 0 ≤ x ^ a := Real.rpow_nonneg hx.1.le _
        have h2 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
        nlinarith
    _ = ENNReal.ofReal (∫ x in Ioc 0 t, x ^ a) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact Real.rpow_nonneg hx.1.le _
    _ = ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
        rw [← intervalIntegral.integral_of_le ht, integral_rpow (Or.inl ha),
          Real.zero_rpow (by linarith), sub_zero]

end NLAlib

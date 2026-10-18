import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NLAlib.ForMathlib.Analysis.ExpBounds

/-!+# Second-order integral remainders

The exact integral Taylor remainder on the unit interval and its exponential
comparison coefficient, including the zero parameter. These real-variable
facts support one-sided trace-exponential replacement estimates.
-/

noncomputable section

open MeasureTheory Set

namespace NLAlib

/-- The continuous integral coefficient in the second-order exponential
remainder. Its definition includes the zero parameter without division. -/
def expSecondRemainderCoefficient (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * r)

/-- The second-order Taylor formula on the unit interval, with the exact
integral remainder and ordinary derivatives. -/
theorem eq_add_deriv_add_integral_iteratedDeriv_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    f 1 = f 0 + deriv f 0 +
      ∫ t in (0 : ℝ)..1, (1 - t) * iteratedDeriv 2 f t := by
  have hfc : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv 1 (by norm_num)
  have hfcc : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (u := fun t : ℝ => 1 - t) (u' := fun _ : ℝ => -1)
    (v := deriv f) (v' := iteratedDeriv 2 f)
    (continuous_const.sub continuous_id).continuousOn hfc.continuousOn
    (fun t _ => by convert! (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1; simp)
    (fun t _ => by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (hfdd t).hasDerivAt)
    intervalIntegrable_const (hfcc.intervalIntegrable 0 1)
  have hint := intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hfd t) (hfc.intervalIntegrable 0 1)
  simp only [sub_self, zero_mul, sub_zero, one_mul, neg_one_mul,
    intervalIntegral.integral_neg, hint] at hparts
  linarith

/-- The exact second-order remainder is bounded using a one-sided exponential
bound on the second derivative. No lower bound on the derivative is needed. -/
theorem le_add_deriv_add_mul_expSecondRemainderCoefficient {f : ℝ → ℝ} {r c : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, iteratedDeriv 2 f t ≤ Real.exp (t * r) * c) :
    f 1 ≤ f 0 + deriv f 0 + c * expSecondRemainderCoefficient r := by
  rw [eq_add_deriv_add_integral_iteratedDeriv_two hf]
  apply add_le_add le_rfl
  rw [expSecondRemainderCoefficient, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((continuous_const.sub continuous_id).mul
      (hf.continuous_iteratedDeriv 2 le_rfl)).intervalIntegrable 0 1
  · exact (continuous_const.mul ((continuous_const.sub continuous_id).mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const)))).intervalIntegrable 0 1
  · intro t ht
    calc
      _ ≤ (1 - t) * (Real.exp (t * r) * c) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (sub_nonneg.mpr ht.2)
      _ = _ := by ring

/-- The integral exponential coefficient is nonnegative at every real parameter. -/
theorem expSecondRemainderCoefficient_nonneg (r : ℝ) :
    0 ≤ expSecondRemainderCoefficient r := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (sub_nonneg.mpr ht.2) (Real.exp_pos _).le

/-- At the zero parameter the continuous exponential remainder coefficient
is one half. -/
@[simp] theorem expSecondRemainderCoefficient_zero :
    expSecondRemainderCoefficient 0 = 1 / 2 := by
  simp only [expSecondRemainderCoefficient, mul_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => t) intervalIntegrable_const
    (continuous_id.intervalIntegrable (0 : ℝ) 1)]
  norm_num [integral_id]

/-- Multiplication by the squared parameter removes the integral in the
exponential remainder coefficient. The identity also holds at zero. -/
theorem sq_mul_expSecondRemainderCoefficient (r : ℝ) :
    r ^ 2 * expSecondRemainderCoefficient r = Real.exp r - 1 - r := by
  have hderiv : deriv (fun t : ℝ => Real.exp (t * r)) =
      fun t => Real.exp (t * r) * r := by
    funext t
    simpa only [id_eq, one_mul] using (((hasDerivAt_id t).mul_const r).exp).deriv
  have hsecond : iteratedDeriv 2 (fun t : ℝ => Real.exp (t * r)) =
      fun t => r ^ 2 * Real.exp (t * r) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv]
    funext t
    have h := ((((hasDerivAt_id t).mul_const r).exp).mul_const r).deriv
    simp only [id_eq, one_mul] at h
    exact h.trans (by ring)
  have h := eq_add_deriv_add_integral_iteratedDeriv_two
    (f := fun t : ℝ => Real.exp (t * r)) (by fun_prop)
  rw [hderiv, hsecond] at h
  simp only [one_mul, zero_mul, Real.exp_zero] at h
  have heq : (∫ t in (0 : ℝ)..1, (1 - t) * (r ^ 2 * Real.exp (t * r))) =
      r ^ 2 * expSecondRemainderCoefficient r := by
    rw [expSecondRemainderCoefficient, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [heq] at h
  linarith

/-- Away from zero the integral coefficient is the usual exponential quotient;
the integral definition supplies its removable value at zero. -/
theorem expSecondRemainderCoefficient_eq_div {r : ℝ} (hr : r ≠ 0) :
    expSecondRemainderCoefficient r = (Real.exp r - 1 - r) / r ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
  simpa only [mul_comm] using sq_mul_expSecondRemainderCoefficient r

/-- The exponential remainder coefficient is continuous at every parameter,
including the removable point zero. -/
theorem continuous_expSecondRemainderCoefficient :
    Continuous expSecondRemainderCoefficient := by
  have hcont : Continuous (Function.uncurry
      (fun r t : ℝ => (1 - t) * Real.exp (t * r))) := by
    fun_prop
  have h := continuous_parametric_integral_of_continuous
    (μ := volume) hcont (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  change Continuous (fun r => expSecondRemainderCoefficient r)
  simpa only [expSecondRemainderCoefficient,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc] using h

/-- The exponential remainder coefficient is monotone in the parameter. -/
theorem monotone_expSecondRemainderCoefficient :
    Monotone expSecondRemainderCoefficient := by
  intro r s hrs
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((continuous_const.sub continuous_id).mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  · exact ((continuous_const.sub continuous_id).mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  · intro t ht
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrs ht.1))
      (sub_nonneg.mpr ht.2)

/-- At nonnegative parameters the coefficient is at least its value one half
at zero. -/
theorem one_half_le_expSecondRemainderCoefficient {r : ℝ} (hr : 0 ≤ r) :
    1 / 2 ≤ expSecondRemainderCoefficient r := by
  simpa only [expSecondRemainderCoefficient_zero] using
    monotone_expSecondRemainderCoefficient hr

/-- Bernstein's scalar exponential bound controls the exact integral
remainder coefficient up to the pole at three, including the zero parameter.
Source: Tropp (2015), Lemma 6.6.2; Tropp (2026), Section 4.9. -/
theorem expSecondRemainderCoefficient_le_div {r : ℝ} (hr : r < 3) :
    expSecondRemainderCoefficient r ≤ (1 / 2) / (1 - r / 3) := by
  by_cases hzero : r = 0
  · simp [hzero]
  have hb := exp_mul_le_one_add_mul_add_sq_mul_of_le
    (L := r) (θ := (1 : ℝ)) (x := r) (by norm_num) (by simpa using hr) le_rfl
  simp only [one_mul, one_pow] at hb
  apply (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hzero)).mp
  rw [sq_mul_expSecondRemainderCoefficient]
  nlinarith

end NLAlib

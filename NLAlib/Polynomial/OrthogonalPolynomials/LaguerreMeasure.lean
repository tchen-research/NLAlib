import NLAlib.Polynomial.OrthogonalPolynomials.Laguerre
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Half-line integral interpretation of the finite Laguerre moments

Finite Laplace moments and the finite Laguerre Gram matrix are identified with
ordinary Lebesgue integrals. Source: reciprocal exponential certificates
(RC3)--(RC6) in the operator re-derivations.
-/

noncomputable section
open Polynomial MeasureTheory Set
open scoped Nat
namespace NLAlib

/-- Every monomial is integrable against a positive exponential weight on the
positive half-line. Source: reciprocal exponential certificate (RC5). -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x^n * Real.exp (-(s*x))) (Ioi 0) := by
  have hb : IntegrableOn (fun x : ℝ => x^n * Real.exp (-x)) (Ioi 0) := by
    convert (Real.GammaIntegral_convergent (by positivity : 0 < (n : ℝ) + 1))
      using 1
    ext x
    simp only [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
  have hc := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x^n * Real.exp (-x)) 0 hs).mpr (by simpa using hb)
  refine IntegrableOn.congr_fun (hc.const_mul (s^n)⁻¹) ?_ measurableSet_Ioi
  intro x _
  simp only [mul_pow, mul_assoc]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hs.ne'), one_mul]

/-- The finite Laplace monomial moment is `n!/s^(n+1)`.
Source: reciprocal exponential certificate (RC5). -/
theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ in Ioi 0, x^n * Real.exp (-(s*x))) = (n ! : ℝ) / s^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : 0 < (n : ℝ) + 1) hs
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  rw [show (n : ℝ) + 1 = ((n+1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at h
  rw [h]
  simp [div_eq_mul_inv, mul_comm]

/-- A polynomial is integrable against every positive exponential weight.
Source: reciprocal exponential certificate (RC5). -/
theorem integrableOn_eval_mul_exp_neg_mul_Ioi (p : ℝ[X]) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => p.eval x * Real.exp (-(s*x))) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    exact (hp.add hq).congr_fun (by intro x _; simp [add_mul]) measurableSet_Ioi
  | monomial n a =>
    exact IntegrableOn.congr_fun ((integrableOn_pow_mul_exp_neg_mul_Ioi n hs).const_mul a)
      (by intro x _; simp [mul_assoc]) measurableSet_Ioi

/-- The finite polynomial moment functional equals integration against its
positive exponential density. Source: reciprocal exponential certificate (RC5). -/
theorem integral_eval_mul_exp_neg_mul_Ioi (p : ℝ[X]) {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ in Ioi 0, p.eval x * Real.exp (-(s*x))) =
      exponentialPolynomialMoment s p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, add_mul, map_add]
    rw [integral_add (integrableOn_eval_mul_exp_neg_mul_Ioi p hs)
      (integrableOn_eval_mul_exp_neg_mul_Ioi q hs), hp, hq]
  | monomial n a =>
    simp only [eval_monomial, mul_assoc]
    rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi n hs,
      exponentialPolynomialMoment_monomial]
    ring

/-- The finite classical Laguerre Gram matrix for the exponential density is
the identity. Source: reciprocal exponential certificate (RC6).
atlas: exp-rational-halfline (partial) -/
theorem integral_laguerrePolynomial_mul_laguerrePolynomial (i j : ℕ) :
    (∫ x : ℝ in Ioi 0, (laguerrePolynomial i).eval x *
      (laguerrePolynomial j).eval x * Real.exp (-x)) = if i = j then 1 else 0 := by
  simpa only [eval_mul, one_mul] using
    (integral_eval_mul_exp_neg_mul_Ioi
      (laguerrePolynomial i * laguerrePolynomial j) zero_lt_one).trans
      (exponentialPolynomialMoment_laguerrePolynomial_mul_laguerrePolynomial i j)

/-- The finite Fourier--Laguerre coefficient of `exp (x/4)` is a geometric term.
Source: reciprocal exponential certificate (RC6). -/
theorem integral_exp_quarter_mul_laguerrePolynomial (n : ℕ) :
    (∫ x : ℝ in Ioi 0, Real.exp (x / 4) *
      (laguerrePolynomial n).eval x * Real.exp (-x)) =
      4 * (-1 : ℝ)^n / 3^(n+1) := by
  have heq : (fun x : ℝ => Real.exp (x / 4) *
      (laguerrePolynomial n).eval x * Real.exp (-x)) =
      (fun x : ℝ => (laguerrePolynomial n).eval x * Real.exp (-((3/4)*x))) := by
    ext x
    rw [mul_comm (Real.exp (x/4)), mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_eval_mul_exp_neg_mul_Ioi _ (by norm_num),
    exponentialPolynomialMoment_laguerrePolynomial (by norm_num)]
  rw [show (3 : ℝ)/4 - 1 = (-1)/4 by norm_num]
  rw [div_pow, div_pow, pow_succ]
  field_simp
  ring

end NLAlib

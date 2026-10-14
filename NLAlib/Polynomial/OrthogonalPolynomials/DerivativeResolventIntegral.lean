import NLAlib.ForMathlib.Algebra.Polynomial.DerivativeResolvent
import NLAlib.Polynomial.OrthogonalPolynomials.LaguerreMeasure
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential tail integrals of finite polynomial resolvents

The finite inverse of `a I-D` has its ordinary exponential tail-integral
interpretation. This verifies the two resolvents in the explicit reciprocal
denominator without differentiating an improper integral.
Source: Section 1 of the focused mathematical re-derivations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

private theorem tendsto_eval_mul_exp_neg_mul (p : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(a*x))) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul, add_zero] using hp.add hq
  | monomial n c =>
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) a ha
    simp only [Real.rpow_natCast] at h
    simpa only [eval_monomial, mul_assoc, mul_zero, neg_mul] using h.const_mul c

/-- A finite derivative resolvent equals the exponentially weighted polynomial
tail integral for every positive decay rate and nonnegative starting point.
Source: explicit reciprocal denominator, finite polynomial integration by parts. -/
theorem derivativeResolvent_eval_mul_exp_neg_eq_integral_Ioi {a : ℝ} (ha : 0 < a)
    (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    (derivativeResolvent a p).eval x * Real.exp (-(a*x)) =
      ∫ t : ℝ in Ioi x, p.eval t * Real.exp (-(a*t)) := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun t : ℝ => (derivativeResolvent a p).eval t * Real.exp (-(a*t)))
      (-(p.eval t * Real.exp (-(a*t)))) t := by
    have h := (derivativeResolvent a p).hasDerivAt t |>.mul
      ((((hasDerivAt_id t).const_mul a).neg).exp)
    have he := congrArg (fun q : ℝ[X] => q.eval t)
      (derivative_derivativeResolvent ha.ne' p)
    simp only [eval_sub, eval_smul, smul_eq_mul] at he
    have hd : (derivativeResolvent a p).derivative.eval t * Real.exp (-(a*t)) +
        (derivativeResolvent a p).eval t * (Real.exp (-(a*t)) * (-a)) =
        -(p.eval t * Real.exp (-(a*t))) := by rw [he]; ring
    convert! h using 1
    simpa only [id_eq, Pi.neg_apply, mul_one] using hd.symm
  have hint := (integrableOn_eval_mul_exp_neg_mul_Ioi p ha).mono_set (Ioi_subset_Ioi hx)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hderiv t) hint.neg
    (tendsto_eval_mul_exp_neg_mul (derivativeResolvent a p) ha)
  rw [integral_neg, zero_sub] at h
  linarith

/-- The growing exponential's weighted tail integral for rates above one quarter.
Source: explicit reciprocal denominator, the fixed exponential mode. -/
theorem integral_exp_quarter_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 1/4 < a) (x : ℝ) :
    (∫ t : ℝ in Ioi x, Real.exp (t/4) * Real.exp (-(a*t))) =
      Real.exp ((1/4-a)*x) / (a-1/4) := by
  have heq : (fun t : ℝ => Real.exp (t/4) * Real.exp (-(a*t))) =
      (fun t : ℝ => Real.exp ((1/4-a)*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_exp_mul_Ioi (by linarith : 1/4-a < 0)]
  rw [show (a-1/4 : ℝ) = -(1/4-a) by ring, div_neg, neg_div]

/-- The exponential resolvent tail integrand is integrable at every starting point.
Source: explicit reciprocal denominator, the fixed exponential mode. -/
theorem integrableOn_exp_quarter_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 1/4 < a) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (t/4) * Real.exp (-(a*t))) (Ioi x) := by
  refine IntegrableOn.congr_fun (integrableOn_exp_mul_Ioi (by linarith : 1/4-a < 0) x)
    ?_ measurableSet_Ioi
  intro t _
  change Real.exp ((1/4-a)*t) = Real.exp (t/4) * Real.exp (-(a*t))
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exact error of a finite polynomial resolvent against the exponential
mode is a weighted residual tail integral. Source: the two-resolvent reroute. -/
theorem derivativeResolvent_error_eq_exp_tail_integral {a : ℝ} (ha : 1/4 < a)
    (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x/4) / (a-1/4) - (derivativeResolvent a p).eval x =
      Real.exp (a*x) * ∫ t : ℝ in Ioi x,
        (Real.exp (t/4) - p.eval t) * Real.exp (-(a*t)) := by
  have ha0 : 0 < a := by linarith
  have hp := (integrableOn_eval_mul_exp_neg_mul_Ioi p ha0).mono_set (Ioi_subset_Ioi hx)
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_exp_quarter_mul_exp_neg_mul_Ioi ha x) hp,
    integral_exp_quarter_mul_exp_neg_mul_Ioi ha,
    ← derivativeResolvent_eval_mul_exp_neg_eq_integral_Ioi ha0 p hx]
  have h1 : Real.exp (a*x) * Real.exp ((1/4-a)*x) = Real.exp (x/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (a*x) * Real.exp (-(a*x)) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp (a*x) * Real.exp ((1/4-a)*x))/(a-1/4) -
        (derivativeResolvent a p).eval x * (Real.exp (a*x) * Real.exp (-(a*x))) := by
          rw [h1, h2, mul_one]
    _ = _ := by ring

end NLAlib

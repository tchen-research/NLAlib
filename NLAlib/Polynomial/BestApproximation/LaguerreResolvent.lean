import NLAlib.Polynomial.BestApproximation.LaguerreProjection
import NLAlib.ForMathlib.MeasureTheory.WeightedCauchySchwarz
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A finite derivative resolvent for exponential approximation

The inverse of `I-D` on polynomials is Mathlib's finite `sumIDeriv` map.
Applying it to the finite Laguerre projection yields the weighted uniform
certificate (RC9), through a half-line tail integral and weighted Cauchy--Schwarz.
Source: reciprocal exponential certificates (RC8)--(RC9).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

private theorem tendsto_eval_mul_exp_neg (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-x)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul, add_zero] using hp.add hq
  | monomial n a =>
    simpa only [eval_monomial, mul_assoc, mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul a

/-- The finite derivative sum is the exact exponential tail integral of a
polynomial, for every nonnegative starting point.
Source: reciprocal exponential certificate (RC9), finite integration by parts. -/
theorem sumIDeriv_eval_mul_exp_neg_eq_integral_Ioi (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    (sumIDeriv p).eval x * Real.exp (-x) =
      ∫ t : ℝ in Ioi x, p.eval t * Real.exp (-t) := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun t : ℝ => (sumIDeriv p).eval t * Real.exp (-t))
      (-(p.eval t * Real.exp (-t))) t := by
    have h := (sumIDeriv p).hasDerivAt t |>.mul ((hasDerivAt_neg t).exp)
    have he := congrArg (fun q : ℝ[X] => q.eval t) (sumIDeriv_eq_self_add p)
    simp only [eval_add] at he
    have ht := congrArg (fun a : ℝ => a * Real.exp (-t)) he
    have hd : (sumIDeriv p).derivative.eval t * Real.exp (-t) +
        (sumIDeriv p).eval t * (Real.exp (-t) * -1) =
        -(p.eval t * Real.exp (-t)) := by nlinarith
    rw [hd] at h
    convert! h using 1
  have hint0 : IntegrableOn (fun t : ℝ => p.eval t * Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul] using integrableOn_eval_mul_exp_neg_mul_Ioi p zero_lt_one
  have hint := hint0.mono_set (Ioi_subset_Ioi hx)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hderiv t)
    hint.neg (tendsto_eval_mul_exp_neg (sumIDeriv p))
  rw [integral_neg, zero_sub] at h
  linarith

/-- The explicit degree-`n` finite derivative resolvent of the Laguerre projection.
Source: reciprocal exponential certificate (RC9). -/
def laguerreExponentialResolvent (n : ℕ) : ℝ[X] :=
  (3/4 : ℝ) • sumIDeriv (laguerreExponentialProjection n)

private theorem integral_exp_neg_Ioi (x : ℝ) :
    (∫ t : ℝ in Ioi x, Real.exp (-t)) = Real.exp (-x) := by
  exact _root_.integral_exp_neg_Ioi x

private theorem integral_exp_quarter_mul_exp_neg_Ioi (x : ℝ) :
    (∫ t : ℝ in Ioi x, Real.exp (t/4) * Real.exp (-t)) =
      (4/3) * Real.exp (-((3/4)*x)) := by
  have heq : (fun t : ℝ => Real.exp (t/4) * Real.exp (-t)) =
      (fun t : ℝ => Real.exp ((-3/4)*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  have h := integral_exp_mul_Ioi (by norm_num : (-3/4 : ℝ) < 0) x
  rw [h]
  norm_num
  ring

private theorem integrableOn_exp_quarter_mul_exp_neg_Ioi (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (t/4) * Real.exp (-t)) (Ioi x) := by
  refine IntegrableOn.congr_fun
    (integrableOn_exp_mul_Ioi (by norm_num : (-3/4 : ℝ) < 0) x)
    ?_ measurableSet_Ioi
  intro t _
  change Real.exp ((-3/4)*t) = Real.exp (t/4) * Real.exp (-t)
  rw [← Real.exp_add]
  congr 1
  ring

private theorem resolvent_error_eq_tail_integral (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x/4) - (laguerreExponentialResolvent n).eval x =
      ((3/4) * Real.exp x) *
        ∫ t : ℝ in Ioi x,
          (Real.exp (t/4) - (laguerreExponentialProjection n).eval t) * Real.exp (-t) := by
  have hp0 : IntegrableOn
      (fun t : ℝ => (laguerreExponentialProjection n).eval t * Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul] using
      integrableOn_eval_mul_exp_neg_mul_Ioi (laguerreExponentialProjection n) zero_lt_one
  have hp := hp0.mono_set (Ioi_subset_Ioi hx)
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_exp_quarter_mul_exp_neg_Ioi x) hp,
    integral_exp_quarter_mul_exp_neg_Ioi,
    ← sumIDeriv_eval_mul_exp_neg_eq_integral_Ioi _ hx,
    laguerreExponentialResolvent, eval_smul, smul_eq_mul]
  have h1 : Real.exp x * Real.exp (-((3/4)*x)) = Real.exp (x/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp x * Real.exp (-((3/4)*x))) -
        (3/4) * (sumIDeriv (laguerreExponentialProjection n)).eval x *
          (Real.exp x * Real.exp (-x)) := by rw [h1, h2]; ring
    _ = _ := by ring

/-- The finite Laguerre derivative resolvent has degree at most `n`.
Source: reciprocal exponential certificate (RC9). -/
theorem degree_laguerreExponentialResolvent_le (n : ℕ) :
    (laguerreExponentialResolvent n).degree ≤ n := by
  have hdeg : (sumIDeriv (laguerreExponentialProjection n)).degree ≤ n := by
    rw [sumIDeriv_apply]
    apply mem_degreeLE.mp
    apply Submodule.sum_mem
    intro j _
    apply mem_degreeLE.mpr
    have h : ∀ k : ℕ, ((derivative : ℝ[X] → ℝ[X])^[k]
        (laguerreExponentialProjection n)).degree ≤ (laguerreExponentialProjection n).degree := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact degree_derivative_le.trans ih
    exact (h j).trans (degree_laguerreExponentialProjection_le n)
  exact (degree_smul_le _ _).trans hdeg

/-- The explicit finite Laguerre derivative resolvent attains the geometric
weighted error bound `sqrt 2 / (4*3^n)` on the full positive half-line.
Source: reciprocal exponential certificate (RC9).
atlas: exp-rational-halfline (partial) -/
theorem abs_exp_quarter_sub_laguerreExponentialResolvent_le (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (x/4) - (laguerreExponentialResolvent n).eval x| ≤
      Real.sqrt 2 / (4 * 3^n) * Real.exp (x/2) := by
  let p := laguerreExponentialProjection n
  let r : ℝ → ℝ := fun t => Real.exp (t/4) - p.eval t
  have hp0 : IntegrableOn (fun t : ℝ => p.eval t * Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul] using integrableOn_eval_mul_exp_neg_mul_Ioi p zero_lt_one
  have hp := hp0.mono_set (Ioi_subset_Ioi hx)
  have hr : IntegrableOn (fun t => r t * Real.exp (-t)) (Ioi x) := by
    refine IntegrableOn.congr_fun ((integrableOn_exp_quarter_mul_exp_neg_Ioi x).sub hp)
      ?_ measurableSet_Ioi
    intro t _
    change Real.exp (t/4) * Real.exp (-t) - p.eval t * Real.exp (-t) =
      (Real.exp (t/4) - p.eval t) * Real.exp (-t)
    ring
  have hsq0 : IntegrableOn (fun t => (r t)^2 * Real.exp (-t)) (Ioi 0) :=
    integrableOn_exp_quarter_sub_eval_sq_mul_exp_neg p
  have hsq := hsq0.mono_set (Ioi_subset_Ioi hx)
  have hC := sq_integral_mul_le_integral_sq_mul_mul_integral
    (μ := volume.restrict (Ioi x)) (fun t => (Real.exp_pos (-t)).le)
    hr hsq (integrableOn_exp_neg_Ioi x)
  rw [integral_exp_neg_Ioi] at hC
  have htotal : (∫ t : ℝ in Ioi 0, (r t)^2 * Real.exp (-t)) = 2 / 3^(2*n+2) := by
    have h := integral_exp_quarter_sub_eval_sq_eq_laguerreResidual_add
      (degree_laguerreExponentialProjection_le n)
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      integral_zero, add_zero] at h
    exact h
  have htail : (∫ t : ℝ in Ioi x, (r t)^2 * Real.exp (-t)) ≤ 2 / 3^(2*n+2) := by
    rw [← htotal]
    apply setIntegral_mono_set hsq0
    · exact Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    · exact Eventually.of_forall (Ioi_subset_Ioi hx)
  have hC' := hC.trans (mul_le_mul_of_nonneg_right htail (Real.exp_pos (-x)).le)
  have hfactor := mul_le_mul_of_nonneg_left hC' (sq_nonneg ((3/4) * Real.exp x))
  have herror := resolvent_error_eq_tail_integral n hx
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hsqexpHalf : (Real.exp (x/2))^2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpow : (3 : ℝ)^(2*n+2) = ((3 : ℝ)^n)^2 * 9 := by
    rw [pow_add, show 2*n = n*2 by omega, pow_mul]
    norm_num
  have hbound : (((3/4) * Real.exp x)^2 *
      ((2 : ℝ) / 3^(2*n+2) * Real.exp (-x))) =
      (Real.sqrt 2 / (4 * 3^n) * Real.exp (x/2))^2 := by
    simp only [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      hsqexpHalf, hpow]
    field_simp
    nlinarith [hcancel]
  rw [hbound] at hfactor
  have hsquared : (Real.exp (x/4) - (laguerreExponentialResolvent n).eval x)^2 ≤
      (Real.sqrt 2 / (4 * 3^n) * Real.exp (x/2))^2 := by
    rw [herror, mul_pow]
    exact hfactor
  have hnonneg : 0 ≤ Real.sqrt 2 / (4 * 3^n) * Real.exp (x/2) := by positivity
  exact (sq_le_sq₀ (abs_nonneg _) hnonneg).mp (by simpa only [sq_abs] using hsquared)

end NLAlib

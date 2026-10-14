import NLAlib.Polynomial.BestApproximation.LaguerreProjection
import NLAlib.Polynomial.OrthogonalPolynomials.DerivativeResolventIntegral
import NLAlib.ForMathlib.MeasureTheory.WeightedCauchySchwarz
import NLAlib.Polynomial.BestApproximation.ExponentialSmoothingKernel

/-!
# The explicit two-resolvent exponential denominator

The denominator is an actual finite polynomial with rational coefficients.
Its finite derivative expression and leading coefficient are exact.
Source: Section 1 of `four_focused_mathematical_reroutes.tex`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
open scoped Nat
namespace NLAlib

/-- The two-resolvent polynomial `H_n` in the focused reciprocal reroute.
The displayed combination is the finite polynomial
`(15/26) * ((3/4 I-D)^(-1) - (4 I-D)^(-1)) g_n`. -/
def doubleResolventExponentialDenominator (n : ℕ) : ℝ[X] :=
  (15/26 : ℝ) • (derivativeResolvent (3/4) (laguerreExponentialProjection n) -
    derivativeResolvent 4 (laguerreExponentialProjection n))

/-- The explicit reciprocal denominator for `exp (-t)`, after the variable
rescaling `x=4t`. Degree zero uses the constant one.
Source: the focused reciprocal reroute. -/
def reciprocalExponentialDenominator (n : ℕ) : ℝ[X] :=
  if n=0 then 1 else (doubleResolventExponentialDenominator n).comp (C 4 * X)

/-- The two resolvents give the advertised finite derivative formula.
Source: the focused reciprocal reroute, explicit denominator formula. -/
theorem doubleResolventExponentialDenominator_eq_sum (n : ℕ) :
    doubleResolventExponentialDenominator n = (15/26 : ℝ) •
      ∑ r ∈ Finset.range (n+1),
        ((4/3 : ℝ)^(r+1) - (1/4 : ℝ)^(r+1)) •
          (derivative : ℝ[X] → ℝ[X])^[r] (laguerreExponentialProjection n) := by
  have hn := natDegree_le_of_degree_le (degree_laguerreExponentialProjection_le n)
  rw [doubleResolventExponentialDenominator,
    derivativeResolvent_apply_of_le hn (3/4), derivativeResolvent_apply_of_le hn 4]
  rw [show ((3/4 : ℝ)⁻¹) = 4/3 by norm_num, show ((4 : ℝ)⁻¹) = 1/4 by norm_num]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]

/-- The two-resolvent denominator preserves the allowed degree.
Source: the focused reciprocal reroute. -/
theorem degree_doubleResolventExponentialDenominator_le (n : ℕ) :
    (doubleResolventExponentialDenominator n).degree ≤ n := by
  apply degree_le_of_natDegree_le
  have hn := natDegree_le_of_degree_le (degree_laguerreExponentialProjection_le n)
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  exact max_le ((natDegree_derivativeResolvent_le _ _).trans hn)
    ((natDegree_derivativeResolvent_le _ _).trans hn)

/-- The top coefficient is positive and explicit, so the denominator has its
full advertised degree. Source: the focused reciprocal reroute. -/
theorem coeff_doubleResolventExponentialDenominator_self (n : ℕ) :
    (doubleResolventExponentialDenominator n).coeff n =
      (5/8 : ℝ) * (4 / (3^(n+1) * (n ! : ℝ))) := by
  have hn := natDegree_le_of_degree_le (degree_laguerreExponentialProjection_le n)
  rw [doubleResolventExponentialDenominator, coeff_smul, coeff_sub,
    coeff_derivativeResolvent_of_natDegree_le (by norm_num : (3/4 : ℝ) ≠ 0) hn,
    coeff_derivativeResolvent_of_natDegree_le (by norm_num : (4 : ℝ) ≠ 0) hn,
    coeff_laguerreExponentialProjection_self, smul_eq_mul]
  ring

/-- The explicit two-resolvent polynomial has degree exactly `n`.
Source: the focused reciprocal reroute. -/
theorem natDegree_doubleResolventExponentialDenominator (n : ℕ) :
    (doubleResolventExponentialDenominator n).natDegree = n := by
  apply le_antisymm (natDegree_le_of_degree_le (degree_doubleResolventExponentialDenominator_le n))
  apply le_natDegree_of_ne_zero
  rw [coeff_doubleResolventExponentialDenominator_self]
  positivity

private theorem shifted_exp_residual_eq (a x t : ℝ) (p : ℝ[X]) :
    Real.exp (-a*(t-x)) * (Real.exp (t/4) - p.eval t) =
      Real.exp (a*x) * ((Real.exp (t/4) - p.eval t) * Real.exp (-(a*t))) := by
  have he : Real.exp (-a*(t-x)) = Real.exp (a*x) * Real.exp (-(a*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

private theorem integrableOn_weighted_exp_residual {a : ℝ} (ha : 1/4 < a)
    (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      (Real.exp (t/4) - p.eval t) * Real.exp (-(a*t))) (Ioi x) := by
  have hp := (integrableOn_eval_mul_exp_neg_mul_Ioi p (by linarith : 0 < a)).mono_set
    (Ioi_subset_Ioi hx)
  refine IntegrableOn.congr_fun ((integrableOn_exp_quarter_mul_exp_neg_mul_Ioi ha x).sub hp)
    ?_ measurableSet_Ioi
  intro t _
  change Real.exp (t/4) * Real.exp (-(a*t)) - p.eval t * Real.exp (-(a*t)) = _
  ring

private theorem integrableOn_shifted_exp_residual {a : ℝ} (ha : 1/4 < a)
    (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => Real.exp (-a*(t-x)) *
      (Real.exp (t/4) - p.eval t)) (Ioi x) := by
  simp_rw [shifted_exp_residual_eq]
  exact (integrableOn_weighted_exp_residual ha p hx).const_mul _

private theorem integral_two_rate_residual (A B x : ℝ) (p : ℝ[X]) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi x,
      (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x))) *
        (Real.exp (t/4) - p.eval t)) =
      A*(Real.exp (x/4)/(3/4-1/4) - (derivativeResolvent (3/4) p).eval x) +
      B*(Real.exp (x/4)/(4-1/4) - (derivativeResolvent 4 p).eval x) := by
  have heq : (fun t : ℝ =>
      (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x))) *
        (Real.exp (t/4) - p.eval t)) =
      (fun t => A*(Real.exp (-(3/4)*(t-x))*(Real.exp (t/4)-p.eval t)) +
        B*(Real.exp (-4*(t-x))*(Real.exp (t/4)-p.eval t))) := by funext t; ring
  rw [heq, integral_add
    ((integrableOn_shifted_exp_residual (by norm_num : (1:ℝ)/4 < 3/4) p hx).const_mul A)
    ((integrableOn_shifted_exp_residual (by norm_num : (1:ℝ)/4 < 4) p hx).const_mul B)]
  simp_rw [integral_const_mul, shifted_exp_residual_eq]
  rw [integral_const_mul, integral_const_mul,
    ← derivativeResolvent_error_eq_exp_tail_integral (by norm_num : (1:ℝ)/4 < 3/4) p hx,
    ← derivativeResolvent_error_eq_exp_tail_integral (by norm_num : (1:ℝ)/4 < 4) p hx]

private theorem integrableOn_two_rate_residual (A B x : ℝ) (p : ℝ[X]) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x))) *
        (Real.exp (t/4) - p.eval t)) (Ioi x) := by
  refine IntegrableOn.congr_fun
    (((integrableOn_shifted_exp_residual (by norm_num : (1:ℝ)/4 < 3/4) p hx).const_mul A).add
      ((integrableOn_shifted_exp_residual (by norm_num : (1:ℝ)/4 < 4) p hx).const_mul B))
    ?_ measurableSet_Ioi
  intro t _
  change A*(Real.exp (-(3/4)*(t-x))*(Real.exp (t/4)-p.eval t)) +
    B*(Real.exp (-4*(t-x))*(Real.exp (t/4)-p.eval t)) = _
  ring

private theorem abs_integral_kernel_laguerreResidual_le (n : ℕ) {x c : ℝ} (hx : 0 ≤ x)
    (hc : 0 ≤ c) (K : ℝ → ℝ)
    (hKi : IntegrableOn (fun t => K (t-x)^2 * Real.exp t) (Ioi x))
    (hKn : (∫ t : ℝ in Ioi x, K (t-x)^2 * Real.exp t) = c*Real.exp x)
    (hKr : IntegrableOn (fun t => K (t-x) *
      (Real.exp (t/4) - (laguerreExponentialProjection n).eval t)) (Ioi x)) :
    |∫ t : ℝ in Ioi x, K (t-x) *
      (Real.exp (t/4) - (laguerreExponentialProjection n).eval t)| ≤
        Real.sqrt (2*c/9) / 3^n * Real.exp (x/2) := by
  let r : ℝ → ℝ := fun t => Real.exp (t/4) - (laguerreExponentialProjection n).eval t
  let F : ℝ → ℝ := fun t => r t * Real.exp (-t/2)
  let G : ℝ → ℝ := fun t => K (t-x) * Real.exp (t/2)
  have hfg : (fun t => F t * G t) = (fun t => K (t-x) * r t) := by
    funext t
    have he : Real.exp (-t/2) * Real.exp (t/2) = 1 := by
      rw [← Real.exp_add, show -t/2+t/2 = 0 by ring, Real.exp_zero]
    dsimp [F, G]
    calc
      _ = (K (t-x)*r t) * (Real.exp (-t/2)*Real.exp (t/2)) := by ring
      _ = _ := by rw [he, mul_one]
  have hF : (fun t => (F t)^2) = (fun t => (r t)^2 * Real.exp (-t)) := by
    funext t
    dsimp [F]
    rw [mul_pow, pow_two (Real.exp (-t/2)), ← Real.exp_add]
    congr 2
    ring
  have hG : (fun t => (G t)^2) = (fun t => K (t-x)^2 * Real.exp t) := by
    funext t
    dsimp [G]
    rw [mul_pow, pow_two (Real.exp (t/2)), ← Real.exp_add]
    congr 2
    ring
  have hs0 := integrableOn_exp_quarter_sub_eval_sq_mul_exp_neg (laguerreExponentialProjection n)
  have hs : IntegrableOn (fun t => (r t)^2 * Real.exp (-t)) (Ioi x) :=
    hs0.mono_set (Ioi_subset_Ioi hx)
  have hfgInt : IntegrableOn (fun t => F t * G t) (Ioi x) := by rw [hfg]; exact hKr
  have hFInt : IntegrableOn (fun t => (F t)^2) (Ioi x) := by rw [hF]; exact hs
  have hGInt : IntegrableOn (fun t => (G t)^2) (Ioi x) := by rw [hG]; exact hKi
  have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq hfgInt hFInt hGInt
  rw [hfg, hF, hG, hKn] at hCS
  have htotal : (∫ t : ℝ in Ioi 0, (r t)^2 * Real.exp (-t)) = 2/3^(2*n+2) := by
    have h := integral_exp_quarter_sub_eval_sq_eq_laguerreResidual_add
      (degree_laguerreExponentialProjection_le n)
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      integral_zero, add_zero] at h
    exact h
  have htail : (∫ t : ℝ in Ioi x, (r t)^2 * Real.exp (-t)) ≤ 2/3^(2*n+2) := by
    rw [← htotal]
    exact setIntegral_mono_set hs0
      (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi hx))
  have hsq := hCS.trans (mul_le_mul_of_nonneg_right htail (mul_nonneg hc (Real.exp_pos x).le))
  have hpow : (3 : ℝ)^(2*n+2) = ((3 : ℝ)^n)^2 * 9 := by
    rw [pow_add, show 2*n = n*2 by omega, pow_mul]
    norm_num
  have hbound : ((2 : ℝ)/3^(2*n+2))*(c*Real.exp x) =
      (Real.sqrt (2*c/9) / 3^n * Real.exp (x/2))^2 := by
    have he : (Real.exp (x/2))^2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), he, hpow]
    field_simp
  rw [hbound] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

/-- The exact value error of the explicit denominator is its smoothing-kernel
integral of the finite Laguerre residual. Source: the focused reciprocal reroute. -/
theorem exp_quarter_sub_doubleResolventExponentialDenominator_eq_integral
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x/4) - (doubleResolventExponentialDenominator n).eval x =
      ∫ t : ℝ in Ioi x, exponentialSmoothingKernel (t-x) *
        (Real.exp (t/4) - (laguerreExponentialProjection n).eval t) := by
  have heq : (fun t : ℝ => exponentialSmoothingKernel (t-x) *
      (Real.exp (t/4) - (laguerreExponentialProjection n).eval t)) =
      (fun t => (15/26 : ℝ) *
        ((1*Real.exp (-(3/4)*(t-x)) + (-1)*Real.exp (-4*(t-x))) *
          (Real.exp (t/4) - (laguerreExponentialProjection n).eval t))) := by
    funext t
    dsimp [exponentialSmoothingKernel]
    ring
  rw [heq, integral_const_mul, integral_two_rate_residual _ _ _ _ hx,
    doubleResolventExponentialDenominator, eval_smul, eval_sub, smul_eq_mul]
  ring

/-- The exact derivative error is the second smoothing-kernel integral of the
finite residual, obtained from the polynomial ODE without differentiating an
improper integral. Source: the focused reciprocal reroute. -/
theorem exp_quarter_div_four_sub_derivative_doubleResolventExponentialDenominator_eq_integral
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x/4)/4 - (doubleResolventExponentialDenominator n).derivative.eval x =
      ∫ t : ℝ in Ioi x, exponentialSmoothingDerivativeKernel (t-x) *
        (Real.exp (t/4) - (laguerreExponentialProjection n).eval t) := by
  have heq : (fun t : ℝ => exponentialSmoothingDerivativeKernel (t-x) *
      (Real.exp (t/4) - (laguerreExponentialProjection n).eval t)) =
      (fun t => (15/26 : ℝ) *
        (((3/4)*Real.exp (-(3/4)*(t-x)) + (-4)*Real.exp (-4*(t-x))) *
          (Real.exp (t/4) - (laguerreExponentialProjection n).eval t))) := by
    funext t
    dsimp [exponentialSmoothingDerivativeKernel]
    ring
  rw [heq, integral_const_mul, integral_two_rate_residual _ _ _ _ hx,
    doubleResolventExponentialDenominator, derivative_smul, derivative_sub,
    derivative_derivativeResolvent (by norm_num : (3/4 : ℝ) ≠ 0),
    derivative_derivativeResolvent (by norm_num : (4 : ℝ) ≠ 0)]
  simp only [eval_smul, eval_sub, smul_eq_mul]
  ring

/-- The explicit two-resolvent denominator has the claimed value error bound.
Source: focused reciprocal reroute, the exact kernel square norm.
atlas: exp-rational-halfline (partial) -/
theorem abs_exp_quarter_sub_doubleResolventExponentialDenominator_le (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (x/4) - (doubleResolventExponentialDenominator n).eval x| ≤
      Real.sqrt (5/42) / 3^n * Real.exp (x/2) := by
  rw [exp_quarter_sub_doubleResolventExponentialDenominator_eq_integral n hx]
  apply (by norm_num : (2 : ℝ)*(15/28)/9 = 5/42) ▸
    abs_integral_kernel_laguerreResidual_le n hx (by norm_num : (0:ℝ) ≤ 15/28)
      exponentialSmoothingKernel (integrableOn_exponentialSmoothingKernel_sq x)
      (integral_exponentialSmoothingKernel_sq x) ?_
  refine IntegrableOn.congr_fun
    ((integrableOn_two_rate_residual 1 (-1) x (laguerreExponentialProjection n) hx).const_mul
      (15/26 : ℝ)) ?_ measurableSet_Ioi
  intro t _
  dsimp [exponentialSmoothingKernel]
  ring

/-- The explicit denominator has the simultaneous derivative error bound.
Source: focused reciprocal reroute, the exact derivative-kernel square norm.
atlas: exp-rational-halfline (partial) -/
theorem abs_exp_quarter_div_four_sub_derivative_doubleResolventExponentialDenominator_le
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (x/4)/4 - (doubleResolventExponentialDenominator n).derivative.eval x| ≤
      Real.sqrt (15/112) / 3^n * Real.exp (x/2) := by
  rw [exp_quarter_div_four_sub_derivative_doubleResolventExponentialDenominator_eq_integral n hx]
  apply (by norm_num : (2 : ℝ)*(135/224)/9 = 15/112) ▸
    abs_integral_kernel_laguerreResidual_le n hx (by norm_num : (0:ℝ) ≤ 135/224)
      exponentialSmoothingDerivativeKernel (integrableOn_exponentialSmoothingDerivativeKernel_sq x)
      (integral_exponentialSmoothingDerivativeKernel_sq x) ?_
  refine IntegrableOn.congr_fun
    ((integrableOn_two_rate_residual (3/4) (-4) x (laguerreExponentialProjection n) hx).const_mul
      (15/26 : ℝ)) ?_ measurableSet_Ioi
  intro t _
  dsimp [exponentialSmoothingDerivativeKernel]
  ring

end NLAlib

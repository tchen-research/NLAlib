import NLAlib.Polynomial.OrthogonalPolynomials.DerivativeResolventIntegral

/-!
# Exact square integrals of the two exponential smoothing kernels

The value kernel and its integration-by-parts derivative kernel have exact
finite square norms. Source: Section 1 of the focused reciprocal reroute.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
namespace NLAlib

/-- The positive value smoothing kernel of the explicit denominator.
Source: focused reciprocal reroute. -/
def exponentialSmoothingKernel (u : ℝ) : ℝ :=
  (15/26) * (Real.exp (-(3/4)*u) - Real.exp (-4*u))

/-- The integration-by-parts derivative kernel, equal to `-k'`.
Source: focused reciprocal reroute. -/
def exponentialSmoothingDerivativeKernel (u : ℝ) : ℝ :=
  (15/26) * ((3/4)*Real.exp (-(3/4)*u) - 4*Real.exp (-4*u))

private theorem shifted_rate_density_eq (s x t : ℝ) :
    Real.exp (-s*(t-x)) * Real.exp t = Real.exp (s*x) * Real.exp ((1-s)*t) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem integrableOn_shifted_rate_density {s : ℝ} (hs : 1 < s) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*(t-x)) * Real.exp t) (Ioi x) := by
  simp_rw [shifted_rate_density_eq]
  exact (integrableOn_exp_mul_Ioi (by linarith : 1-s < 0) x).const_mul _

private theorem integral_shifted_rate_density {s : ℝ} (hs : 1 < s) (x : ℝ) :
    (∫ t : ℝ in Ioi x, Real.exp (-s*(t-x)) * Real.exp t) =
      Real.exp x / (s-1) := by
  simp_rw [shifted_rate_density_eq]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : 1-s < 0)]
  have hc : -Real.exp ((1-s)*x)/(1-s) = Real.exp ((1-s)*x)/(s-1) := by
    field_simp [show 1-s ≠ 0 by linarith, show s-1 ≠ 0 by linarith]
    ring
  rw [hc, ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem two_rate_sq_density (A B x t : ℝ) :
    (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x)))^2 * Real.exp t =
      A^2 * (Real.exp (-(3/2)*(t-x)) * Real.exp t) +
      (2*A*B) * (Real.exp (-(19/4)*(t-x)) * Real.exp t) +
      B^2 * (Real.exp (-8*(t-x)) * Real.exp t) := by
  have ha : (Real.exp (-(3/4)*(t-x)))^2 = Real.exp (-(3/2)*(t-x)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb : (Real.exp (-4*(t-x)))^2 = Real.exp (-8*(t-x)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hab : Real.exp (-(3/4)*(t-x)) * Real.exp (-4*(t-x)) =
      Real.exp (-(19/4)*(t-x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = A^2 * ((Real.exp (-(3/4)*(t-x)))^2 * Real.exp t) +
      (2*A*B) * ((Real.exp (-(3/4)*(t-x)) * Real.exp (-4*(t-x))) * Real.exp t) +
      B^2 * ((Real.exp (-4*(t-x)))^2 * Real.exp t) := by ring
    _ = _ := by rw [ha, hab, hb]

private theorem integrableOn_two_rate_sq_density (A B x : ℝ) :
    IntegrableOn (fun t : ℝ =>
      (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x)))^2 * Real.exp t) (Ioi x) := by
  simp_rw [two_rate_sq_density]
  exact (((integrableOn_shifted_rate_density (by norm_num : 1 < (3:ℝ)/2) x).const_mul _).add
    ((integrableOn_shifted_rate_density (by norm_num : 1 < (19:ℝ)/4) x).const_mul _)).add
    ((integrableOn_shifted_rate_density (by norm_num : (1:ℝ) < 8) x).const_mul _)

private theorem integral_two_rate_sq_density (A B x : ℝ) :
    (∫ t : ℝ in Ioi x,
      (A*Real.exp (-(3/4)*(t-x)) + B*Real.exp (-4*(t-x)))^2 * Real.exp t) =
      Real.exp x * (2*A^2 + (8/15)*A*B + (1/7)*B^2) := by
  simp_rw [two_rate_sq_density]
  have hA := (integrableOn_shifted_rate_density (by norm_num : 1 < (3:ℝ)/2) x).const_mul (A^2)
  have hAB := (integrableOn_shifted_rate_density (by norm_num : 1 < (19:ℝ)/4) x).const_mul (2*A*B)
  have hB := (integrableOn_shifted_rate_density (by norm_num : (1:ℝ) < 8) x).const_mul (B^2)
  have hadd := integral_add (hA.add hAB) hB
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hA hAB]
  simp_rw [integral_const_mul]
  rw [integral_shifted_rate_density (by norm_num : 1 < (3:ℝ)/2),
    integral_shifted_rate_density (by norm_num : 1 < (19:ℝ)/4),
    integral_shifted_rate_density (by norm_num : (1:ℝ) < 8)]
  ring

/-- The value kernel square density is integrable at every shifted starting point.
Source: the focused reciprocal reroute. -/
theorem integrableOn_exponentialSmoothingKernel_sq (x : ℝ) :
    IntegrableOn (fun t : ℝ => (exponentialSmoothingKernel (t-x))^2 * Real.exp t) (Ioi x) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_two_rate_sq_density 1 (-1) x).const_mul ((15/26 : ℝ)^2))
    ?_ measurableSet_Ioi
  intro t _
  dsimp [exponentialSmoothingKernel]
  ring

/-- The derivative kernel square density is integrable at every shifted starting point.
Source: the focused reciprocal reroute. -/
theorem integrableOn_exponentialSmoothingDerivativeKernel_sq (x : ℝ) :
    IntegrableOn (fun t : ℝ => (exponentialSmoothingDerivativeKernel (t-x))^2 * Real.exp t) (Ioi x) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_two_rate_sq_density (3/4) (-4) x).const_mul ((15/26 : ℝ)^2))
    ?_ measurableSet_Ioi
  intro t _
  dsimp [exponentialSmoothingDerivativeKernel]
  ring

/-- The exact value-kernel square integral is `(15/28) exp x`.
Source: the focused reciprocal reroute. -/
theorem integral_exponentialSmoothingKernel_sq (x : ℝ) :
    (∫ t : ℝ in Ioi x, (exponentialSmoothingKernel (t-x))^2 * Real.exp t) =
      (15/28)*Real.exp x := by
  have heq : (fun t : ℝ => (exponentialSmoothingKernel (t-x))^2 * Real.exp t) =
      (fun t : ℝ => (15/26 : ℝ)^2 *
        ((1*Real.exp (-(3/4)*(t-x)) + (-1)*Real.exp (-4*(t-x)))^2 * Real.exp t)) := by
    funext t
    dsimp [exponentialSmoothingKernel]
    ring
  rw [heq, integral_const_mul, integral_two_rate_sq_density]
  ring

/-- The exact derivative-kernel square integral is `(135/224) exp x`.
Source: the focused reciprocal reroute. -/
theorem integral_exponentialSmoothingDerivativeKernel_sq (x : ℝ) :
    (∫ t : ℝ in Ioi x, (exponentialSmoothingDerivativeKernel (t-x))^2 * Real.exp t) =
      (135/224)*Real.exp x := by
  have heq : (fun t : ℝ => (exponentialSmoothingDerivativeKernel (t-x))^2 * Real.exp t) =
      (fun t : ℝ => (15/26 : ℝ)^2 *
        (((3/4)*Real.exp (-(3/4)*(t-x)) + (-4)*Real.exp (-4*(t-x)))^2 * Real.exp t)) := by
    funext t
    dsimp [exponentialSmoothingDerivativeKernel]
    ring
  rw [heq, integral_const_mul, integral_two_rate_sq_density]
  ring

end NLAlib

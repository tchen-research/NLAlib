import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integration by parts around a circle

Holomorphic functions on a neighborhood of a circle satisfy contour
integration by parts. In particular, the integral of `exp z * h'(z)` is the
negative of the integral of `exp z * h(z)`. This supplies the integration by
parts step of the inverse-contour bridge toward `trace-exponential-stahl`.
-/

noncomputable section

open Set Metric Complex

namespace circleIntegral

/-- Contour integration by parts on a circle follows from the product
primitive. Both functions need only be holomorphic on a neighborhood of the
circle; the disk interior need not belong to their domain. -/
theorem integral_mul_deriv_eq_neg_integral_deriv_mul
    {f g : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hU : IsOpen U) (hc : sphere c r ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    (∮ z in C(c, r), f z * deriv g z) =
      -(∮ z in C(c, r), deriv f z * g z) := by
  have hfd : ContinuousOn (deriv f) U := (hf.deriv hU).continuousOn
  have hgd : ContinuousOn (deriv g) U := (hg.deriv hU).continuousOn
  have hleft : CircleIntegrable (fun z => deriv f z * g z) c r :=
    ((hfd.mul hg.continuousOn).mono hc).circleIntegrable hr
  have hright : CircleIntegrable (fun z => f z * deriv g z) c r :=
    ((hf.continuousOn.mul hgd).mono hc).circleIntegrable hr
  have hzero : (∮ z in C(c, r), deriv f z * g z + f z * deriv g z) = 0 := by
    apply integral_eq_zero_of_hasDerivWithinAt hr
    intro z hz
    exact ((hf.differentiableAt (hU.mem_nhds (hc hz))).hasDerivAt.mul
      (hg.differentiableAt (hU.mem_nhds (hc hz))).hasDerivAt).hasDerivWithinAt
  rw [integral_add hleft hright] at hzero
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hzero)

/-- Moving the derivative from a holomorphic factor to the exponential
changes the sign of the circle integral. This applies on exterior domains
and therefore does not assume holomorphy inside the circle. -/
theorem integral_exp_mul_deriv_eq_neg_integral_exp_mul
    {h : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hU : IsOpen U) (hc : sphere c r ⊆ U)
    (hh : DifferentiableOn ℂ h U) :
    (∮ z in C(c, r), exp z * deriv h z) =
      -(∮ z in C(c, r), exp z * h z) := by
  simpa only [Complex.deriv_exp] using
    integral_mul_deriv_eq_neg_integral_deriv_mul hr hU hc
      Complex.differentiable_exp.differentiableOn hh

end circleIntegral

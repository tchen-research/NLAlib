import NLAlib.Probability.Gaussian.Calculus.IntegrationByParts
import NLAlib.ForMathlib.MeasureTheory.Integral
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Gaussian integration by parts under integrability hypotheses

Stein's identity for unbounded differentiable functions and its coordinate
tensorization. The operator hard-edge proof uses polynomially bounded smooth
regularizations, so integrability replaces boundedness assumptions.

Source: Stein's Gaussian integration by parts and the scalar integration API
in IntegrationByParts. Atlas: gaussian-integration-by-parts and
wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- Coordinate Stein identity on a finite product of standard Gaussian laws.
Source: scalar Gaussian integration by parts and one-coordinate resampling;
atlas gaussian-integration-by-parts and wishart-lambda-min-tail.
atlas: gaussian-integration-by-parts -/
theorem integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (df : (ι → ℝ) → ℝ) (i : ι)
    (hupdate : ∀ x t, HasDerivAt (fun y => f (Function.update x i y))
      (df (Function.update x i t)) t)
    (hfi : Integrable f (gaussianVector ι))
    (hxfi : Integrable (fun x => x i * f x)
      (gaussianVector ι))
    (hdfi : Integrable (fun x => df x)
      (gaussianVector ι)) :
    (∫ x : ι → ℝ, x i * f x ∂(gaussianVector _)) =
      ∫ x : ι → ℝ, df x
        ∂(gaussianVector _) := by
  let γ : ι → Measure ℝ := fun _ => gaussianReal 0 1
  have hleft :=
    integral_integral_update_pi γ i hxfi
  have hright :=
    integral_integral_update_pi γ i hdfi
  have hsections :
      ∀ᵐ x ∂(Measure.pi γ),
        (∫ t, t * f (Function.update x i t) ∂(gaussianReal 0 1)) =
        ∫ t, df (Function.update x i t)
          ∂(gaussianReal 0 1) := by
    filter_upwards [ae_integrable_comp_update_pi γ i hfi,
      ae_integrable_comp_update_pi γ i hxfi,
      ae_integrable_comp_update_pi γ i hdfi] with x h1 h2 h3
    have hd (t : ℝ) :
        HasDerivAt (fun y => f (Function.update x i y))
          (df (Function.update x i t)) t :=
      hupdate x t
    have hdiff : Differentiable ℝ (fun t => f (Function.update x i t)) :=
      fun t => (hd t).differentiableAt
    have hdeq : deriv (fun t => f (Function.update x i t)) =
        fun t => df (Function.update x i t) :=
      funext fun t => (hd t).deriv
    have hdi : Integrable (deriv (fun t => f (Function.update x i t)))
        (gaussianReal 0 1) := by
      rw [hdeq]
      exact h3
    have hi := integral_mul_eq_integral_deriv_gaussianReal_of_integrable
      (fun t => f (Function.update x i t)) hdiff h1
      (by simpa only [Function.update_self] using h2) hdi
    simpa only [hdeq] using hi
  calc
    _ = (∫ x : ι → ℝ, ∫ t, t * f (Function.update x i t) ∂(gaussianReal 0 1)
        ∂(Measure.pi γ)) := by
      simpa only [Function.update_self] using hleft.symm
    _ = (∫ x : ι → ℝ, ∫ t,
        df (Function.update x i t)
          ∂(gaussianReal 0 1) ∂(Measure.pi γ)) :=
      integral_congr_ae hsections
    _ = _ := hright

/-- The coordinate Stein identity written using the Fréchet derivative of a
differentiable function. Source: scalar Gaussian integration by parts and
coordinate resampling; atlas gaussian-integration-by-parts.
atlas: gaussian-integration-by-parts -/
theorem integral_coordinate_mul_eq_integral_fderiv_gaussian
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (i : ι)
    (hfi : Integrable f (gaussianVector ι))
    (hxfi : Integrable (fun x => x i * f x)
      (gaussianVector ι))
    (hdfi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1))
      (gaussianVector ι)) :
    (∫ x : ι → ℝ, x i * f x ∂(gaussianVector _)) =
      ∫ x : ι → ℝ, fderiv ℝ f x (Pi.single i 1)
        ∂(gaussianVector _) := by
  apply integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update f
    (fun x => fderiv ℝ f x (Pi.single i 1)) i _ hfi hxfi hdfi
  intro x t
  exact (hf (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update x i t)

end NLAlib

import NLAlib.Gaussian.Concentration.IntegrationByParts
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

/-- Gaussian integration by parts for an unbounded differentiable function whose
value, coordinate product, and derivative are integrable. Source: Stein 1981,
Lemma 1; atlas gaussian-integration-by-parts (operator hard-edge helper).
atlas: gaussian-integration-by-parts -/
theorem integral_mul_eq_integral_deriv_gaussianReal_of_integrable
    (h : ℝ → ℝ) (hh : Differentiable ℝ h)
    (hhi : Integrable h (gaussianReal 0 1))
    (hxh : Integrable (fun x => x * h x) (gaussianReal 0 1))
    (hdi : Integrable (deriv h) (gaussianReal 0 1)) :
    (∫ x, x * h x ∂(gaussianReal 0 1)) =
      ∫ x, deriv h x ∂(gaussianReal 0 1) := by
  let φ := gaussianPDFReal 0 1
  rw [integrable_gaussianReal_iff] at hxh hdi hhi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h)
    (v := fun x => -φ x) (u' := deriv h) (v' := fun x => x * φ x)
    (fun x _ => (hh x).hasDerivAt)
    (fun x _ => ((hasDerivAt_gaussianPDFReal_zero 1 one_ne_zero x).neg).congr_deriv
      (by simp [φ]))
    (by
      have : (h * fun x => x * φ x) = fun x => φ x * (x * h x) := by
        funext x; simp; ring
      rw [this]; exact hxh)
    (by
      have : (deriv h * fun x => -φ x) = fun x => -(φ x * deriv h x) := by
        funext x; simp; ring
      rw [this]; exact hdi.neg)
    (by
      have : (h * fun x => -φ x) = fun x => -(φ x * h x) := by
        funext x; simp; ring
      rw [this]; exact hhi.neg)
  have e1 : (fun x => φ x * (x * h x)) = fun x => h x * (x * φ x) := by
    funext x; ring
  have e2 : (fun x => φ x * deriv h x) = fun x => -(deriv h x * -φ x) := by
    funext x; ring
  rw [e1, key, e2, integral_neg]

/-- Coordinate Stein identity on a finite product of standard Gaussian laws.
Source: scalar Gaussian integration by parts and one-coordinate resampling;
atlas gaussian-integration-by-parts and wishart-lambda-min-tail.
atlas: gaussian-integration-by-parts -/
theorem integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (df : (ι → ℝ) → ℝ) (i : ι)
    (hupdate : ∀ x t, HasDerivAt (fun y => f (Function.update x i y))
      (df (Function.update x i t)) t)
    (hfi : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxfi : Integrable (fun x => x i * f x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdfi : Integrable (fun x => df x)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ x : ι → ℝ, x i * f x ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ x : ι → ℝ, df x
        ∂(Measure.pi fun _ => gaussianReal 0 1) := by
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
    (hfi : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxfi : Integrable (fun x => x i * f x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdfi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ x : ι → ℝ, x i * f x ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ x : ι → ℝ, fderiv ℝ f x (Pi.single i 1)
        ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  apply integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update f
    (fun x => fderiv ℝ f x (Pi.single i 1)) i _ hfi hxfi hdfi
  intro x t
  exact (hf (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update x i t)

end NLAlib

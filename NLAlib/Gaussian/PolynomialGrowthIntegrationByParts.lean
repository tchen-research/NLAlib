import NLAlib.Gaussian.Concentration.Stein
import NLAlib.Gaussian.Moments.FourthMoment
import NLAlib.ForMathlib.MeasureTheory.Integral

/-!
# Gaussian integration by parts on polynomial-growth domains

The derivative and Gaussian multiplication operators are formal adjoints.
The integration-by-parts identity holds on the integrable derivative domain,
and polynomial growth provides the needed integrability automatically.

Source: Stein's identity; Vershynin 2018, Lemma 7.2.3.
Atlas: `gaussian-integration-by-parts`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

/-- Every polynomial growth majorant is integrable under a standard Gaussian.
Source: finiteness of all Gaussian moments; atlas `gaussian-integration-by-parts`. -/
theorem integrable_one_add_abs_pow_gaussianReal (d : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ d) (gaussianReal 0 1) := by
  have hX := (memLp_id_gaussianReal (μ := 0) (v := 1) (d : NNReal)).norm
  have h := ((memLp_const (1 : ℝ)).add hX).integrable_norm_pow'
  simp only [Pi.add_apply, id_eq, Real.norm_eq_abs] at h
  convert h using 1
  funext x
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 + |x|)]

/-- Measurable functions of polynomial growth have finite Gaussian first moments.
Source: Gaussian moments; atlas `gaussian-integration-by-parts`. -/
theorem integrable_gaussianReal_of_polynomial_growth
    {f : ℝ → ℝ} (hf : AEMeasurable f (gaussianReal 0 1))
    (C : ℝ) (d : ℕ) (hBound : ∀ x, |f x| ≤ C * (1 + |x|) ^ d) :
    Integrable f (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_one_add_abs_pow_gaussianReal d).const_mul C)
    hf.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hBound x

/-- Stein's identity for differentiable functions whose values and derivatives
have polynomial growth. All integrability premises are derived from the growth
bounds. Source: Stein's identity; atlas `gaussian-integration-by-parts`. -/
theorem integral_mul_eq_integral_deriv_gaussianReal_of_polynomial_growth
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (C D : ℝ) (d e : ℕ)
    (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d)
    (hDeriv : ∀ x, |deriv f x| ≤ D * (1 + |x|) ^ e) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, deriv f x ∂gaussianReal 0 1 := by
  have hi := integrable_gaussianReal_of_polynomial_growth
    hf.continuous.measurable.aemeasurable C d hValue
  have hdi := integrable_gaussianReal_of_polynomial_growth
    (measurable_deriv f).aemeasurable D e hDeriv
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hxBound (x : ℝ) : |x * f x| ≤ C * (1 + |x|) ^ (d + 1) := by
    rw [abs_mul, pow_succ]
    calc
      |x| * |f x| ≤ |x| * (C * (1 + |x|) ^ d) :=
        mul_le_mul_of_nonneg_left (hValue x) (abs_nonneg x)
      _ ≤ (1 + |x|) * (C * (1 + |x|) ^ d) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC (by positivity))
      _ = C * ((1 + |x|) ^ d * (1 + |x|)) := by ring
  have hxi := integrable_gaussianReal_of_polynomial_growth
    (measurable_id.mul hf.continuous.measurable).aemeasurable C (d + 1) hxBound
  exact integral_mul_eq_integral_deriv_gaussianReal_of_integrable f hf hi hxi hdi

/-- The Gaussian derivative operator is formally adjoint to multiplication
minus differentiation: `⟨Df,g⟩γ = ⟨f,(M-D)g⟩γ`. All four pairings are genuinely
integrable. Source: Gaussian operator integration by parts;
atlas `gaussian-integration-by-parts`. -/
theorem integral_deriv_mul_eq_integral_mul_mul_sub_deriv_gaussianReal
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : Integrable (fun x => f x * g x) (gaussianReal 0 1))
    (hxfg : Integrable (fun x => x * (f x * g x)) (gaussianReal 0 1))
    (hdfg : Integrable (fun x => deriv f x * g x) (gaussianReal 0 1))
    (hfdg : Integrable (fun x => f x * deriv g x) (gaussianReal 0 1)) :
    ∫ x, deriv f x * g x ∂gaussianReal 0 1 =
      ∫ x, f x * (x * g x - deriv g x) ∂gaussianReal 0 1 := by
  have hDiff : Differentiable ℝ (fun x => f x * g x) := hf.mul hg
  have hDeriv : deriv (fun x => f x * g x) =
      fun x => deriv f x * g x + f x * deriv g x := by
    funext x
    exact deriv_mul (hf x) (hg x)
  have hdInt : Integrable (deriv (fun x => f x * g x)) (gaussianReal 0 1) := by
    rw [hDeriv]
    exact hdfg.add hfdg
  have hStein := integral_mul_eq_integral_deriv_gaussianReal_of_integrable
    (fun x => f x * g x) hDiff hfg hxfg hdInt
  rw [hDeriv, integral_add hdfg hfdg] at hStein
  have hRight : (fun x => f x * (x * g x - deriv g x)) =
      (fun x => x * (f x * g x)) - (fun x => f x * deriv g x) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hRight]
  change (∫ x, deriv f x * g x ∂gaussianReal 0 1) =
    ∫ x, x * (f x * g x) - f x * deriv g x ∂gaussianReal 0 1
  rw [integral_sub hxfg hfdg]
  linarith

end NLAlib

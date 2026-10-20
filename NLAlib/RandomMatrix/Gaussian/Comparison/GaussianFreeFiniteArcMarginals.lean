import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteMixedArcs
import NLAlib.Probability.Gaussian.Calculus.StandardCovarianceIntegral
import NLAlib.Matrix.Functions.ResolventMoments
import NLAlib.Matrix.Norms.NormalizedModulusMoments

/-! # The genuine common marginal of correlated native resolvent moments

The actual correlated coordinate vector preserves the canonical Gaussian
law. Consequently all actual even modulus traces have the same expectation
as the original native interpolant, with no marginal-law hypothesis.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Every actual normalized even resolvent modulus moment on the genuine
correlation path has exactly the original native Gaussian expectation.
Endpoint correlations, zero degree, arbitrary mean, and empty dimensions
are included. The common marginal is derived from actual Gaussian rotation.
Source: arXiv:2108.06312v2, Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem integral_normalized_modulus_gaussianFreeFinite_correlation
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (t : ℝ) (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    (∫ w : E × E, (normalizedTrace
      (CFC.abs (resolvent (gaussianFreeFiniteInterpolation A₀ A q
        (t • w.1 + Real.sqrt (1 - t ^ 2) • w.2)) ζ) ^ (2 * p))).re
      ∂(gaussianVector K).prod (gaussianVector K)) =
      ∫ x : E, (normalizedTrace
        (CFC.abs (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) ^ (2 * p))).re
          ∂gaussianVector K := by
  let F : E → ℝ := fun x => (normalizedTrace
    (CFC.abs (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) ^ (2 * p))).re
  have heq (x : E) : F x =
      (normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)).re := by
    have h := re_normalizedTrace_cfcAbs_pow_two_mul
      (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) p
    change F x = (normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)).re
    rw [show F x = resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ p by
      simpa only [F, RCLike.re_eq_complex_re, resolventEvenMoment] using h]
    exact resolventEvenMoment_eq_re_normalizedTrace_mul_pow
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) ζ p
  let T : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hFc : Continuous F := by
    have hf := Complex.reCLM.continuous.comp (T.continuous.comp
      (contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ p p (r := ⊤)).continuous)
    have hEqFn : F = fun x : E =>
        (normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)).re := funext heq
    rw [hEqFn]
    simpa +instances only [T, Function.comp_def, LinearMap.coe_toContinuousLinearMap',
      normalizedTraceLinearMap_apply] using! hf
  exact (measurePreserving_standardGaussianCorrelation (κ := K) t ht ht1).hasLaw.integral_comp
    hFc.aestronglyMeasurable

end NLAlib

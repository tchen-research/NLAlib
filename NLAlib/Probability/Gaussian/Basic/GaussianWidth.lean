import NLAlib.ForMathlib.Analysis.SupportFunction
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian width as expected support

The native standard Gaussian measure on a finite-dimensional real inner-product
space defines ordinary Gaussian width. Compactness yields a continuous support
function and integrability; no random maximizing point is selected.
Source: Tropp 2020, Definition 6.4 and Example 6.5; supplied reroutes W3–W4.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Ordinary Gaussian width, with no absolute value inside the supremum.
For a compact nonempty set it is the finite expected support function. For other
sets this total definition uses the real supremum and Bochner-integral defaults.
Source: Tropp 2020, Definition 6.4.
atlas: gaussian-width-def (partial) -/
def gaussianWidth (T : Set E) : ℝ :=
  ∫ z, realSupportFunction T z ∂stdGaussian E

/-- The support function of a nonempty compact set is integrable against the
standard Gaussian measure. Source: supplied reroute W3.
atlas: gaussian-width-def (partial) -/
theorem integrable_realSupportFunction_stdGaussian {T : Set E} (hT : IsCompact T)
    (hne : T.Nonempty) : Integrable (realSupportFunction T) (stdGaussian E) := by
  obtain ⟨R,hR,hbound⟩ := hT.isBounded.exists_pos_norm_le
  have hn : Integrable (fun z : E => ‖z‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  refine (hn.const_mul R).mono' (continuous_realSupportFunction hT hne).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]
    exact abs_realSupportFunction_le hT hne hbound z

private theorem integrable_inner_right (a : E) :
    Integrable (fun z : E => inner ℝ z a) (stdGaussian E) := by
  have hi := IsGaussian.integrable_dual (stdGaussian E) (innerSL ℝ a)
  change Integrable (fun z : E => inner ℝ a z) (stdGaussian E) at hi
  exact hi.congr (Filter.Eventually.of_forall fun z => (real_inner_comm a z).symm)

private theorem integral_inner_right (a : E) :
    (∫ z : E, inner ℝ z a ∂stdGaussian E) = 0 := by
  simpa only [innerSL_apply_apply, real_inner_comm] using
    integral_strongDual_stdGaussian (innerSL ℝ a)

/-- Reflecting the argument of a compact support function leaves its
standard Gaussian expectation unchanged. -/
theorem integral_realSupportFunction_neg_stdGaussian {T : Set E}
    (hT : IsCompact T) (hne : T.Nonempty) :
    (∫ z : E, realSupportFunction T (-z) ∂stdGaussian E) = gaussianWidth T := by
  let U : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hU : HasLaw U (stdGaussian E) (stdGaussian E) :=
    ⟨U.continuous.measurable.aemeasurable, stdGaussian_map U⟩
  exact hU.integral_comp (integrable_realSupportFunction_stdGaussian hT hne).aestronglyMeasurable

/-- Every nonempty compact set has nonnegative ordinary Gaussian width.
Source: centering of Gaussian linear functionals and supplied reroute W3.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_nonneg {T : Set E} (hT : IsCompact T) (hne : T.Nonempty) :
    0 ≤ gaussianWidth T := by
  obtain ⟨a,ha⟩ := hne
  have h := integral_mono (integrable_inner_right a)
    (integrable_realSupportFunction_stdGaussian hT ⟨a,ha⟩)
    (fun z => inner_le_realSupportFunction hT ha z)
  simpa only [integral_inner_right, gaussianWidth] using h

/-- Translation leaves ordinary Gaussian width unchanged.
Source: Tropp 2020, Example 6.5; supplied reroute W4.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_image_add {T : Set E} (hT : IsCompact T) (hne : T.Nonempty) (a : E) :
    gaussianWidth ((fun x => x+a) '' T) = gaussianWidth T := by
  unfold gaussianWidth
  simp_rw [realSupportFunction_image_add hT hne]
  rw [integral_add (integrable_realSupportFunction_stdGaussian hT hne)
    (integrable_inner_right a), integral_inner_right, add_zero]

/-- A singleton has zero ordinary Gaussian width, irrespective of its location.
Source: Tropp 2020, Example 6.5.
atlas: gaussian-width-def (partial) -/
@[simp] theorem gaussianWidth_singleton (a : E) : gaussianWidth ({a} : Set E) = 0 := by
  simp only [gaussianWidth, realSupportFunction_singleton, integral_inner_right]

/-- Orthogonal changes of coordinates preserve ordinary Gaussian width.
Source: rotation invariance of the native standard Gaussian measure; reroute W4.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_image_linearIsometryEquiv {T : Set E} (hT : IsCompact T)
    (hne : T.Nonempty) (U : E ≃ₗᵢ[ℝ] E) : gaussianWidth (U '' T) = gaussianWidth T := by
  unfold gaussianWidth
  simp_rw [realSupportFunction_image_linearIsometryEquiv]
  have hU : HasLaw U.symm (stdGaussian E) (stdGaussian E) :=
    ⟨U.symm.continuous.measurable.aemeasurable, stdGaussian_map U.symm⟩
  exact hU.integral_comp (integrable_realSupportFunction_stdGaussian hT hne).aestronglyMeasurable

/-- Convexification leaves the support function and Gaussian width unchanged.
Source: Tropp 2020, Example 6.5; supplied reroute W4.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_convexHull {T : Set E} (hT : IsCompact T) (hne : T.Nonempty) :
    gaussianWidth (convexHull ℝ T) = gaussianWidth T := by
  unfold gaussianWidth
  simp_rw [realSupportFunction_convexHull hT hne]

/-- Taking the closed convex hull also leaves Gaussian width unchanged.
Source: supplied reroute W4 and continuity of the defining linear functional.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_closure_convexHull {T : Set E} (hT : IsCompact T) (hne : T.Nonempty) :
    gaussianWidth (closure (convexHull ℝ T)) = gaussianWidth T := by
  unfold gaussianWidth
  simp_rw [realSupportFunction_closure_convexHull hT hne]

/-- Gaussian width is positively homogeneous, including zero scaling.
Source: homogeneity of support functions, supplied Gaussian-width route.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_image_smul {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) : gaussianWidth ((fun x => c • x) '' T) = c * gaussianWidth T := by
  unfold gaussianWidth
  simp_rw [realSupportFunction_image_smul hT hne hc]
  exact integral_const_mul _ _

/-- Inclusion increases the Gaussian width of compact nonempty sets.
Source: monotonicity of the support function.
atlas: gaussian-width-def (partial) -/
theorem gaussianWidth_mono {S T : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    (hT : IsCompact T) (hst : S ⊆ T) : gaussianWidth S ≤ gaussianWidth T := by
  exact integral_mono (integrable_realSupportFunction_stdGaussian hS hne)
    (integrable_realSupportFunction_stdGaussian hT (hne.mono hst))
    (fun z => realSupportFunction_mono hS hne hT hst z)

end NLAlib

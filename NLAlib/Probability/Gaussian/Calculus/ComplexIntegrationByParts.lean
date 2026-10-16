import NLAlib.Probability.Gaussian.Calculus.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Data.Complex.BigOperators

/-!
# Complex-valued tests in real Gaussian integration by parts

The real multivariate identity applies separately to the real and imaginary
parts of an actual bounded complex C¹ test. Integrability of the coordinate
product and all partial derivatives follows from Gaussian moments and the
stated bounds; no integrability or interpolation conclusion is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- A bounded continuous complex test of a Gaussian vector is integrable. -/
theorem integrable_complex_comp_of_hasGaussianLaw
    (V : Ω → ι → ℝ) (hV : HasGaussianLaw V P)
    (G : (ι → ℝ) → ℂ) (hGc : Continuous G) (C : ℝ) (hGb : ∀ x, ‖G x‖ ≤ C) :
    Integrable (fun ω => G (V ω)) P := by
  have := hV.isProbabilityMeasure
  exact Integrable.mono' (integrable_const C)
    (hGc.comp_aestronglyMeasurable hV.aemeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω => hGb _))

/-- A real Gaussian coordinate times a bounded continuous complex test of a
jointly Gaussian vector is integrable. -/
theorem integrable_smul_complex_comp_of_hasGaussianLaw
    (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P)
    (G : (ι → ℝ) → ℂ) (hGc : Continuous G) (C : ℝ) (hGb : ∀ x, ‖G x‖ ≤ C) :
    Integrable (fun ω => U ω • G (fun j => V j ω)) P := by
  have := hUV.isProbabilityMeasure
  have hUi : Integrable U P := hUV.fst.memLp_two.integrable one_le_two
  have hGa := hGc.comp_aestronglyMeasurable hUV.snd.aemeasurable.aestronglyMeasurable
  refine Integrable.mono' (hUi.norm.mul_const C)
    (hUi.aestronglyMeasurable.smul hGa) ?_
  filter_upwards [] with ω
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hGb _) (norm_nonneg _)

/-- Gaussian integration by parts for a bounded complex C¹ test with bounded
continuous complex partial derivatives. The Gaussian coordinates are real and
their actual joint law may be singular; only the first coordinate must be
centered. All Bochner integrability follows from the stated bounds.
Source: the real multivariate Gaussian Stein identity, applied to both parts.
atlas: gaussian-integration-by-parts (partial) -/
theorem integral_smul_eq_sum_covariance_smul_integral_complex
    (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P)
    (hU0 : ∫ ω, U ω ∂P = 0)
    (G : (ι → ℝ) → ℂ) (G' : ι → (ι → ℝ) → ℂ)
    (hG : ∀ x, HasFDerivAt G
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).smulRight
        (G' j x)) x)
    (hG'c : ∀ j, Continuous (G' j)) (C C' : ℝ)
    (hGb : ∀ x, ‖G x‖ ≤ C) (hG'b : ∀ j x, ‖G' j x‖ ≤ C') :
    (∫ ω, U ω • G (fun j => V j ω) ∂P) =
      ∑ j, cov[U, V j; P] • ∫ ω, G' j (fun j => V j ω) ∂P := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hleft := integrable_smul_complex_comp_of_hasGaussianLaw U V hUV G hGc C hGb
  have hpartial (j : ι) : Integrable (fun ω => G' j (fun k => V k ω)) P :=
    integrable_complex_comp_of_hasGaussianLaw _ hUV.snd _ (hG'c j) C' (hG'b j)
  have hRe (x : ι → ℝ) : HasFDerivAt (fun y => (G y).re)
      (∑ j, (G' j x).re • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x := by
    have he : Complex.reCLM.comp (∑ j,
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).smulRight (G' j x)) =
        ∑ j, (G' j x).re • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j := by
      ext y
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, mul_comm]
    have h := Complex.reCLM.hasFDerivAt.comp x (hG x)
    rw [he] at h
    exact h
  have hIm (x : ι → ℝ) : HasFDerivAt (fun y => (G y).im)
      (∑ j, (G' j x).im • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x := by
    have he : Complex.imCLM.comp (∑ j,
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).smulRight (G' j x)) =
        ∑ j, (G' j x).im • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j := by
      ext y
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, mul_comm]
    have h := Complex.imCLM.hasFDerivAt.comp x (hG x)
    rw [he] at h
    exact h
  have hR := integral_mul_eq_sum_covariance_mul_integral U V hUV hU0
    (fun x => (G x).re) (fun j x => (G' j x).re) hRe
    (fun j => Complex.continuous_re.comp (hG'c j)) (max C C')
    (fun x => (Complex.abs_re_le_norm _).trans ((hGb x).trans (le_max_left _ _)))
    (fun j x => (Complex.abs_re_le_norm _).trans ((hG'b j x).trans (le_max_right _ _)))
  have hI := integral_mul_eq_sum_covariance_mul_integral U V hUV hU0
    (fun x => (G x).im) (fun j x => (G' j x).im) hIm
    (fun j => Complex.continuous_im.comp (hG'c j)) (max C C')
    (fun x => (Complex.abs_im_le_norm _).trans ((hGb x).trans (le_max_left _ _)))
    (fun j x => (Complex.abs_im_le_norm _).trans ((hG'b j x).trans (le_max_right _ _)))
  have hrint (f : Ω → ℂ) (hf : Integrable f P) :
      (∫ ω, f ω ∂P).re = ∫ ω, (f ω).re ∂P :=
    (Complex.reCLM.integral_comp_comm hf).symm
  have hiint (f : Ω → ℂ) (hf : Integrable f P) :
      (∫ ω, f ω ∂P).im = ∫ ω, (f ω).im ∂P :=
    (Complex.imCLM.integral_comp_comm hf).symm
  apply Complex.ext
  · rw [hrint _ hleft]
    simp only [Complex.re_sum, Complex.smul_re, smul_eq_mul]
    simp_rw [hrint _ (hpartial _)]
    exact hR
  · rw [hiint _ hleft]
    simp only [Complex.im_sum, Complex.smul_im, smul_eq_mul]
    simp_rw [hiint _ (hpartial _)]
    exact hI

end NLAlib

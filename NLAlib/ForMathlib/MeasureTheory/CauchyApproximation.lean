import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Cauchy probability kernels approximate the identity

An affine change of variables identifies Cauchy regularization with the
actual standard Cauchy probability measure. Dominated convergence then
recovers every bounded continuous test against a finite measure.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ProbabilityTheory

/-- Translation and positive rescaling of the standard Cauchy density. -/
theorem cauchyPDFReal_affine (x t : ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    cauchyPDFReal 0 1 t = (γ : ℝ) * cauchyPDFReal x γ (x + γ * t) := by
  simp only [cauchyPDFReal, NNReal.coe_one, sub_zero, one_pow, mul_one]
  field_simp [hγ, NNReal.coe_ne_zero.mpr hγ]
  ring

/-- Integration against a location-scale Cauchy density is integration
of the corresponding affine argument against the standard Cauchy law. -/
theorem integral_mul_cauchyPDFReal_eq_integral_affine (f : ℝ → ℝ)
    (x : ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    (∫ y : ℝ, f y * cauchyPDFReal x γ y) =
      ∫ t : ℝ, f (x + γ * t) ∂cauchyMeasure 0 1 := by
  rw [cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 1)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [cauchyPDF, ENNReal.toReal_ofReal (le_of_lt (cauchyPDF_pos 0 (γ := (1 : NNReal)) (by norm_num) _)),
    smul_eq_mul]
  have he : (fun t : ℝ => cauchyPDFReal 0 1 t * f (x + γ * t)) =
      fun t : ℝ => (γ : ℝ) * (f (x + γ * t) * cauchyPDFReal x γ (x + γ * t)) := by
    funext t
    rw [cauchyPDFReal_affine x t γ hγ]
    ring
  rw [he, integral_const_mul,
    integral_comp_mul_left (fun y : ℝ => f (x + y) * cauchyPDFReal x γ (x + y)),
    integral_add_left_eq_self (fun y : ℝ => f y * cauchyPDFReal x γ y) x]
  simp only [abs_of_nonneg (inv_nonneg.mpr γ.coe_nonneg), smul_eq_mul]
  field_simp [NNReal.coe_ne_zero.mpr hγ]

/-- Vanishing positive Cauchy scale recovers a bounded continuous test
at every location. No moment assumptions on the Cauchy law are needed. -/
theorem tendsto_integral_affine_cauchy (f : BoundedContinuousFunction ℝ ℝ) (x : ℝ)
    {γ : ℕ → NNReal} (hγ : Tendsto (fun n => (γ n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : ℝ, f (x + γ n * t) ∂cauchyMeasure 0 1)
      atTop (𝓝 (f x)) := by
  have ht (t : ℝ) : Tendsto (fun n => f (x + γ n * t)) atTop (𝓝 (f x)) := by
    apply f.continuous.continuousAt.tendsto.comp
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hγ.mul_const t)
  have h := tendsto_integral_of_dominated_convergence (μ := cauchyMeasure 0 1)
    (fun _ : ℝ => ‖f‖)
    (fun n => (by fun_prop : Continuous (fun t : ℝ => f (x + γ n * t))).aestronglyMeasurable)
    (integrable_const _) (fun _ => Filter.Eventually.of_forall (fun _ => f.norm_coe_le_norm _))
    (Filter.Eventually.of_forall ht)
  simpa using h

end ProbabilityTheory

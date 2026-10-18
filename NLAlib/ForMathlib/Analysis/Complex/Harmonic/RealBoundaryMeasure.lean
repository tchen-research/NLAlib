import NLAlib.ForMathlib.Analysis.Complex.CayleyBoundary
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesNormalization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The positive real measure behind the normalized Herglotz formula

Push the actual stereographically weighted circle measure onto the real
line. Finite vertical mass supplies its finiteness and exact total mass.
The difference formula avoids any assumption on a first moment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology
namespace Complex

/-- The real-line positive measure obtained from a circle Herglotz measure.
Its finiteness is proved from vertical normalization, not included in the definition. -/
def cayleyBoundaryMeasure (μ : Measure Circle) : Measure ℝ :=
  (μ.withDensity (fun ξ : Circle => ENNReal.ofReal (2 / (1 - (ξ : ℂ).re)))).map
    cayleyBoundaryReal

/-- The stereographic weight is measurable, even at the totalized value at `1`. -/
theorem measurable_cayleyBoundaryWeight :
    Measurable (fun ξ : Circle => 2 / (1 - (ξ : ℂ).re)) := by
  fun_prop

/-- Integrability of the stereographic weight makes the real-line measure finite. -/
theorem isFiniteMeasure_cayleyBoundaryMeasure (μ : Measure Circle)
    (hi : Integrable (fun ξ : Circle => 2 / (1 - (ξ : ℂ).re)) μ) :
    IsFiniteMeasure (cayleyBoundaryMeasure μ) := by
  let : IsFiniteMeasure (μ.withDensity (fun ξ : Circle =>
      ENNReal.ofReal (2 / (1 - (ξ : ℂ).re)))) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ξ =>
        div_nonneg (by norm_num) (sub_nonneg.mpr (circle_re_le_one ξ))))).mp
        hi.hasFiniteIntegral).ne
  unfold cayleyBoundaryMeasure
  infer_instance

/-- The weighted real-line mass is exactly the integral of the circle weight. -/
theorem cayleyBoundaryMeasure_real_univ (μ : Measure Circle)
    (hi : Integrable (fun ξ : Circle => 2 / (1 - (ξ : ℂ).re)) μ) :
    (cayleyBoundaryMeasure μ).real univ = ∫ ξ : Circle, 2 / (1 - (ξ : ℂ).re) ∂μ := by
  have hn : ∀ᵐ ξ : Circle ∂μ, 0 ≤ 2 / (1 - (ξ : ℂ).re) :=
    Filter.Eventually.of_forall (fun ξ =>
      div_nonneg (by norm_num) (sub_nonneg.mpr (circle_re_le_one ξ)))
  rw [measureReal_def, cayleyBoundaryMeasure,
    Measure.map_apply measurable_cayleyBoundaryReal MeasurableSet.univ]
  simp only [preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)

/-- Real Cauchy kernels are bounded above the real axis. -/
theorem norm_real_cauchyKernel_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hz
  have h := abs_im_le_norm ((x : ℂ) - z)
  simpa only [sub_im, ofReal_im, zero_sub, abs_neg, abs_of_pos hz] using h

/-- Every finite positive real measure has an integrable Cauchy kernel
at every upper-half-plane point. -/
theorem integrable_real_cauchyKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  apply (integrable_const z.im⁻¹).mono'
  · exact (by fun_prop : Measurable (fun x : ℝ => ((x : ℂ) - z)⁻¹)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => norm_real_cauchyKernel_le x hz)

/-- The finite Cauchy transform is bounded by mass divided by height. -/
theorem norm_integral_real_cauchyKernel_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) :
    ‖∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ‖ ≤ μ.real univ / z.im := by
  calc
    _ ≤ ∫ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : ℝ, z.im⁻¹ ∂μ := integral_mono
      (integrable_real_cauchyKernel μ hz).norm (integrable_const _)
      (fun x => norm_real_cauchyKernel_le x hz)
    _ = _ := by rw [integral_const]; simp only [smul_eq_mul, div_eq_mul_inv]

/-- Cauchy transforms of finite positive measures vanish on the high imaginary axis. -/
theorem tendsto_integral_real_cauchyKernel_mul_I (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun y : ℝ => ∫ x : ℝ, ((x : ℂ) - (y : ℂ) * I)⁻¹ ∂μ)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop (μ.real univ))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have him : 0 < ((y : ℂ) * I).im := by simpa using hy
  simpa using norm_integral_real_cauchyKernel_le μ him
end Complex

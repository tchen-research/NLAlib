import NLAlib.ForMathlib.Analysis.Complex.Harmonic.RealBoundaryMeasure

/-!
# Normalized positive Stieltjes representation

A holomorphic upper-half-plane function with nonnegative imaginary part
and finite Stieltjes normalization is the Cauchy transform of an actual
positive finite real measure. This supplies the scalar analytic bridge
in Ajanki--Erdos--Kruger, Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology
namespace Complex

/-- A circle Herglotz kernel is integrable at every upper-half-plane argument. -/
theorem integrable_herglotzRieszKernel_cayley (μ : Measure Circle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun ξ : Circle => herglotzRieszKernel 0 (cayleyTransform z) ξ) μ := by
  have hc := continuous_herglotzRieszKernel_circle
    (by simpa only [mem_ball, dist_zero_right] using norm_cayleyTransform_lt_one hz)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Subtracting the kernel at `i` cancels the affine coordinate, without
a first-moment assumption on the real measure. -/
theorem sub_I_mul_herglotzRieszKernel_cayley
    {z : ℂ} (hz : 0 < z.im) {ξ : Circle} (hξ : ξ ≠ 1) :
    I * herglotzRieszKernel 0 (cayleyTransform z) ξ -
      I * herglotzRieszKernel 0 (cayleyTransform I) ξ =
    (2 / (1 - (ξ : ℂ).re) : ℝ) •
      (((cayleyBoundaryReal ξ : ℂ) - z)⁻¹ - ((cayleyBoundaryReal ξ : ℂ) - I)⁻¹) := by
  rw [I_mul_herglotzRieszKernel_cayleyTransform hz hξ,
    I_mul_herglotzRieszKernel_cayleyTransform (by simp) hξ,
    ← one_add_sq_cayleyBoundaryReal hξ, Complex.real_smul]
  ring

/-- The circle representation transports to the real-line Cauchy
transform after subtracting its value at `i`. -/
theorem integral_sub_herglotzRieszKernel_cayley_eq
    (μ : Measure Circle) [IsFiniteMeasure μ] (hzero : μ {(1 : Circle)} = 0)
    {z : ℂ} (hz : 0 < z.im) :
    I * (∫ ξ : Circle, herglotzRieszKernel 0 (cayleyTransform z) ξ ∂μ) -
      I * (∫ ξ : Circle, herglotzRieszKernel 0 (cayleyTransform I) ξ ∂μ) =
    ∫ x : ℝ, ((x : ℂ) - z)⁻¹ - ((x : ℂ) - I)⁻¹ ∂cayleyBoundaryMeasure μ := by
  have hI : 0 < I.im := by simp
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub ((integrable_herglotzRieszKernel_cayley μ hz).const_mul I)
      ((integrable_herglotzRieszKernel_cayley μ hI).const_mul I)]
  rw [cayleyBoundaryMeasure, integral_map measurable_cayleyBoundaryReal.aemeasurable
    (by fun_prop : Measurable (fun x : ℝ => ((x : ℂ) - z)⁻¹ -
      ((x : ℂ) - I)⁻¹)).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      measurable_cayleyBoundaryWeight.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  have hae : ∀ᵐ ξ : Circle ∂μ, ξ ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hzero
  filter_upwards [hae] with ξ hξ
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num)
    (sub_nonneg.mpr (circle_re_le_one ξ)))]
  exact sub_I_mul_herglotzRieszKernel_cayley hz hξ

/-- Finite Stieltjes normalization forces decay of the function itself
on the positive imaginary axis. -/
theorem tendsto_zero_of_tendsto_mul_I {f : ℂ → ℂ} {c : ℂ}
    (hlim : Tendsto (fun y : ℝ => (y : ℂ) * I * f ((y : ℂ) * I))
      atTop (𝓝 c)) :
    Tendsto (fun y : ℝ => f ((y : ℂ) * I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ =>
      -I * ((1 / y : ℝ) • ((y : ℂ) * I * f ((y : ℂ) * I)))) atTop (𝓝 0) := by
    simpa only [zero_smul, mul_zero, id_eq] using
      (tendsto_const_nhds (x := -I)).mul
        ((tendsto_id.const_div_atTop (1 : ℝ)).smul hlim)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Complex.real_smul, ofReal_div, ofReal_one]
  field_simp [ne_of_gt hy]
  simp only [I_sq]
  ring

/-- A normalized holomorphic function with nonnegative imaginary part
in the upper half plane is the Cauchy transform of an actual finite
positive measure on the real line. Its mass is the normalization `c`.
No representation, boundary values, or moment assumptions are supplied.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, scalar bridge.
This theorem supplies the scalar foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem _root_.AnalyticOnNhd.exists_finiteMeasure_stieltjes_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (c : NNReal)
    (hlim : Tendsto (fun y : ℝ => (y : ℂ) * I * f ((y : ℂ) * I))
      atTop (𝓝 (-(c : ℝ) : ℂ))) :
    ∃ μ : FiniteMeasure ℝ, μ.mass = c ∧
      ∀ z : ℂ, 0 < z.im → f z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨σ, _hmass, hσ⟩ := hf.exists_finiteMeasure_cayley_integral_eq hpos
  have him (z : ℂ) (hz : 0 < z.im) :
      (f z).im = ∫ ξ : Circle, poissonKernel 0 (cayleyTransform z) ξ ∂(σ : Measure Circle) := by
    rw [hσ z hz]
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
    exact (integral_re (integrable_herglotzRieszKernel_cayley (σ : Measure Circle) hz)).symm.trans
            (integral_congr_ae (Filter.Eventually.of_forall (fun ξ =>
        (congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0)
          (w := cayleyTransform z)) (ξ : ℂ)).symm)))
  have hvertical : Tendsto (fun y : ℝ => y * (f ((y : ℂ) * I)).im)
      atTop (𝓝 (c : ℝ)) := by
    simpa only [Function.comp_apply, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero, zero_sub, neg_neg,
      neg_re, ofReal_re] using ((continuous_re.tendsto _).comp hlim).neg
  have hpoisson : Tendsto (fun y : ℝ => ∫ ξ : Circle,
      y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ ∂(σ : Measure Circle))
        atTop (𝓝 (c : ℝ)) := by
    apply hvertical.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hz : 0 < ((y : ℂ) * I).im := by simpa using hy
    rw [him _ hz, integral_const_mul]
  have hweight := integrable_weight_and_integral_eq_of_tendsto_integral_poissonMass
    (σ : Measure Circle) hpoisson
  have hzero := measure_singleton_one_eq_zero_of_tendsto_integral_poissonMass
    (σ : Measure Circle) hpoisson
  let ν := cayleyBoundaryMeasure (σ : Measure Circle)
  let hν : IsFiniteMeasure ν := isFiniteMeasure_cayleyBoundaryMeasure _ hweight.1
  let μ : FiniteMeasure ℝ := ⟨ν, hν⟩
  have hm : μ.mass = c := by
    apply NNReal.coe_injective
    change ν.real univ = (c : ℝ)
    exact (cayleyBoundaryMeasure_real_univ _ hweight.1).trans hweight.2
  have hdiff (z : ℂ) (hz : 0 < z.im) :
      f z - f I = (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂ν) -
        ∫ x : ℝ, ((x : ℂ) - I)⁻¹ ∂ν := by
    conv_lhs => lhs; rw [hσ z hz]
    conv_lhs => rhs; rw [hσ I (by simp)]
    rw [add_sub_add_left_eq_sub]
    rw [integral_sub_herglotzRieszKernel_cayley_eq (σ : Measure Circle) hzero hz]
    exact integral_sub (integrable_real_cauchyKernel ν hz)
      (integrable_real_cauchyKernel ν (by simp))
  have hconstant : f I - (∫ x : ℝ, ((x : ℂ) - I)⁻¹ ∂ν) = 0 := by
    have hd : Tendsto (fun y : ℝ => f ((y : ℂ) * I) -
        ∫ x : ℝ, ((x : ℂ) - (y : ℂ) * I)⁻¹ ∂ν) atTop (𝓝 0) := by
      simpa only [sub_zero] using (tendsto_zero_of_tendsto_mul_I hlim).sub
        (tendsto_integral_real_cauchyKernel_mul_I ν)
    have he : (fun y : ℝ => f ((y : ℂ) * I) -
        ∫ x : ℝ, ((x : ℂ) - (y : ℂ) * I)⁻¹ ∂ν) =ᶠ[atTop]
        fun _ => f I - ∫ x : ℝ, ((x : ℂ) - I)⁻¹ ∂ν := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hz : 0 < ((y : ℂ) * I).im := by simpa using hy
      linear_combination hdiff ((y : ℂ) * I) hz
    exact tendsto_nhds_unique tendsto_const_nhds (hd.congr' he)
  refine ⟨μ, hm, ?_⟩
  intro z hz
  change f z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂ν
  linear_combination hdiff z hz + hconstant

end Complex

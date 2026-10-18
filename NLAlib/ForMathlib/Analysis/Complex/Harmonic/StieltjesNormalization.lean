import NLAlib.ForMathlib.Analysis.Complex.Harmonic.PoissonMass
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite Stieltjes mass from the upper-half-plane normalization

The vertical Poisson mass tests remove the circle atom at infinity and
control the actual weighted finite mass on the real line. All measures
here are positive native measures, not signed functionals or assumed
representations. Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology

namespace Complex

/-- Every positive-height vertical Poisson mass test is integrable under
an arbitrary finite circle measure. -/
theorem integrable_mul_poissonKernel_cayley_mul_I
    (μ : Measure Circle) [IsFiniteMeasure μ] {y : ℝ} (hy : 0 < y) :
    Integrable (fun ξ : Circle => y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ) μ := by
  have him : 0 < ((y : ℂ) * I).im := by simpa only [mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_one, mul_zero, add_zero] using hy
  have hw : cayleyTransform ((y : ℂ) * I) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right] using norm_cayleyTransform_lt_one him
  exact (continuous_const.mul (continuous_poissonKernel_circle hw)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A finite limit of the vertical Poisson masses excludes an atom at
the missing Cayley boundary point. This removes the linear term in the
upper-half-plane Herglotz representation. -/
theorem measure_singleton_one_eq_zero_of_tendsto_integral_poissonMass
    (μ : Measure Circle) [IsFiniteMeasure μ] {c : ℝ}
    (hlim : Tendsto (fun y : ℝ => ∫ ξ : Circle,
      y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ ∂μ) atTop (𝓝 c)) :
    μ {(1 : Circle)} = 0 := by
  have hsingle (y : ℝ) (hy : 0 < y) :
      μ.real {(1 : Circle)} * y ^ 2 ≤
        ∫ ξ : Circle, y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ ∂μ := by
    have h := setIntegral_le_integral (s := {(1 : Circle)})
      (integrable_mul_poissonKernel_cayley_mul_I μ hy)
      (Filter.Eventually.of_forall (fun ξ => mul_poissonKernel_cayley_mul_I_nonneg ξ hy))
    simpa only [integral_singleton, smul_eq_mul, mul_poissonKernel_cayley_mul_I_one hy] using h
  have hbound : ∀ᶠ y : ℝ in atTop, μ.real {(1 : Circle)} ≤ (c + 1) / y ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (Iio_mem_nhds (lt_add_one c))]
      with y hy hb
    apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
    exact (hsingle y hy).trans hb.le
  have hzero : Tendsto (fun y : ℝ => (c + 1) / y ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (α := ℝ) (show (2 : ℕ) ≠ 0 by decide)).const_div_atTop _
  have hle : μ.real {(1 : Circle)} ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero hbound
  exact (measureReal_eq_zero_iff (μ := μ) (s := {(1 : Circle)})).mp
    (le_antisymm hle measureReal_nonneg)



/-- Finite vertical mass fixes the real-line weight and its exact total
mass. Fatou first establishes integrability; dominated convergence then
recovers equality, without any boundary-value assumption. -/
theorem integrable_weight_and_integral_eq_of_tendsto_integral_poissonMass
    (μ : Measure Circle) [IsFiniteMeasure μ] {c : ℝ}
    (hlim : Tendsto (fun y : ℝ => ∫ ξ : Circle,
      y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ ∂μ) atTop (𝓝 c)) :
    Integrable (fun ξ : Circle => 2 / (1 - (ξ : ℂ).re)) μ ∧
      ∫ ξ : Circle, 2 / (1 - (ξ : ℂ).re) ∂μ = c := by
  let F (n : ℕ) (ξ : Circle) : ℝ :=
    ((n : ℝ) + 1) * poissonKernel 0 (cayleyTransform (Complex.ofReal ((n : ℝ) + 1) * I)) ξ
  let v (ξ : Circle) : ℝ := 2 / (1 - (ξ : ℂ).re)
  have hn (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hy : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi (n : ℕ) : Integrable (F n) μ :=
    by simpa only [F, ofReal_add, ofReal_one, ofReal_natCast] using
      integrable_mul_poissonKernel_cayley_mul_I μ (hn n)
  have hnonneg (n : ℕ) (ξ : Circle) : 0 ≤ F n ξ :=
    by simpa only [F, ofReal_add, ofReal_one, ofReal_natCast] using
      mul_poissonKernel_cayley_mul_I_nonneg ξ (hn n)
  have hvnonneg (ξ : Circle) : 0 ≤ v ξ := by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (circle_re_le_one ξ))
  have hae : ∀ᵐ ξ : Circle ∂μ, ξ ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using
      measure_singleton_one_eq_zero_of_tendsto_integral_poissonMass μ hlim
  have hpoint : ∀ᵐ ξ : Circle ∂μ, Tendsto (fun n => F n ξ) atTop (𝓝 (v ξ)) := by
    filter_upwards [hae] with ξ hξ
    simpa only [F, v, Function.comp_def, ofReal_add, ofReal_one, ofReal_natCast] using
      (tendsto_mul_poissonKernel_cayley_mul_I hξ).comp hy
  have hflim : Tendsto (fun n => ∫ ξ, F n ξ ∂μ) atTop (𝓝 c) := by
    simpa only [F, Function.comp_def, ofReal_add, ofReal_one, ofReal_natCast] using hlim.comp hy
  have hfatou : ∫⁻ ξ, ENNReal.ofReal (v ξ) ∂μ ≤ ENNReal.ofReal c := by
    calc
      _ = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (F n ξ)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with ξ hξ
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hξ).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (F n ξ) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal c := by
        have heq (n : ℕ) : ∫⁻ ξ, ENNReal.ofReal (F n ξ) ∂μ =
            ENNReal.ofReal (∫ ξ, F n ξ ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hi n)
            (Filter.Eventually.of_forall (hnonneg n))).symm
        simp_rw [heq]
        exact ((ENNReal.continuous_ofReal.tendsto c).comp hflim).liminf_eq
  have hv : Integrable v μ := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable)
      hpoint, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hvnonneg)).mpr
      (hfatou.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hv, ?_⟩
  have hdom : ∀ n, ∀ᵐ ξ ∂μ, ‖F n ξ‖ ≤ v ξ := by
    intro n
    filter_upwards [hae] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n ξ)]
    simpa only [F, v, ofReal_add, ofReal_one, ofReal_natCast] using
      mul_poissonKernel_cayley_mul_I_le hξ (hn n)
  exact tendsto_nhds_unique
    (tendsto_integral_of_dominated_convergence v (fun n => (hi n).aestronglyMeasurable)
      hv hdom hpoint) hflim
end Complex

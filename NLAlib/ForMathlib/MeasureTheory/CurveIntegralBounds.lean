import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Curve integral bounds by the integral of speed

The standard length bound for an arbitrary path, expressed using the integral
of its parameter speed. The bound uses Mathlib's native curve integral and
requires integrability of that speed; the smooth-path corollary proves this
integrability from a `C¹` parameterization. No Cauchy formula or winding-number
claim is built into these estimates.
-/

noncomputable section
open MeasureTheory Set
open scoped unitInterval

section Normed
variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}

/-- An arbitrary path integral is bounded by a bound for the operator norm of
its one-form times the integral of its speed. The speed is the derivative
within the parameter interval, so endpoint values agree with the curve-integral
convention. -/
theorem norm_curveIntegral_le_mul_integral_norm_derivWithin
    (ω : E → E →L[𝕜] F) (γ : Path a b) {C : ℝ}
    (hω : ∀ t ∈ Icc (0 : ℝ) 1, ‖ω (γ.extend t)‖ ≤ C)
    (hγ : IntervalIntegrable (fun t => ‖derivWithin γ.extend I t‖) volume 0 1) :
    ‖curveIntegral ω γ‖ ≤ C * ∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun t ht => ?_) (hγ.const_mul C)
  rw [curveIntegralFun_def]
  exact (ω (γ.extend t)).le_of_opNorm_le (hω t (Ioc_subset_Icc_self ht)) _

/-- The integral of speed in the preceding bound is automatically finite for
a path with a `C¹` parameterization. -/
theorem norm_curveIntegral_le_mul_integral_norm_derivWithin_of_contDiffOn
    (ω : E → E →L[𝕜] F) (γ : Path a b) {C : ℝ}
    (hω : ∀ t ∈ Icc (0 : ℝ) 1, ‖ω (γ.extend t)‖ ≤ C)
    (hγ : ContDiffOn ℝ 1 γ.extend I) :
    ‖curveIntegral ω γ‖ ≤ C * ∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖ := by
  apply norm_curveIntegral_le_mul_integral_norm_derivWithin ω γ hω
  have hc : ContinuousOn (fun t => ‖derivWithin γ.extend I t‖) I :=
    (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).norm
  exact hc.intervalIntegrable_of_Icc zero_le_one

end Normed

namespace Complex

/-- A scalar complex contour integral, normalized by `2πi`, obeys the standard
length bound on every path with integrable speed. This estimate alone makes no
claim that the integral equals a value or a quadrature error. -/
theorem norm_two_pi_i_inv_mul_curveIntegral_le_integral_speed_mul
    {a b : ℂ} (γ : Path a b) (g : ℂ → ℂ) {C : ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ‖g (γ.extend t)‖ ≤ C)
    (hγ : IntervalIntegrable (fun t => ‖derivWithin γ.extend I t‖) volume 0 1) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ * curveIntegral
      (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ‖ ≤
      ((∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖) / (2 * Real.pi)) * C := by
  have h := norm_curveIntegral_le_mul_integral_norm_derivWithin
    (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ
    (C := C) (by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hg) hγ
  rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_I, mul_one,
    norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num only [norm_ofNat]
  calc
    (2 * Real.pi)⁻¹ * ‖curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ‖ ≤
        (2 * Real.pi)⁻¹ * (C * ∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (by positivity))
    _ = ((∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖) / (2 * Real.pi)) * C := by ring

end Complex

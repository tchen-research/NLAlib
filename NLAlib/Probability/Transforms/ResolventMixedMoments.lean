import NLAlib.Probability.Transforms.ResolventMoments
import NLAlib.Matrix.Norms.TraceSpectral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual integrable mixed resolvent traces

All laws, expectations and regularity are those of the actual objects.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Actual mixed nonreal Hermitian resolvent traces are integrable under any finite law, including moment order zero and empty dimensions. -/
theorem integrable_normalizedTrace_resolvent_mixed_pow
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) (p : ℕ) :
    Integrable (fun ω => normalizedTrace
      (resolvent (X ω) ζ ^ p * resolvent (X ω) (star ζ) ^ p)) μ := by
  have hstar : (star ζ).im ≠ 0 := by
    simpa only [Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ
  let T : Matrix n n ℂ →L[ℂ] ℂ :=
    (normalizedTraceLinearMap : Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hm : AEStronglyMeasurable (fun ω => normalizedTrace
      (resolvent (X ω) ζ ^ p * resolvent (X ω) (star ζ) ^ p)) μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact T.continuous.measurable.comp_aemeasurable
      (((measurable_matrix_resolvent ζ).comp_aemeasurable hXm).pow_const p |>.mul
        (((measurable_matrix_resolvent (star ζ)).comp_aemeasurable hXm).pow_const p))
  apply Integrable.of_bound hm ((|ζ.im|⁻¹) ^ (2 * p))
  filter_upwards [hX] with ω hω
  have hr : ‖resolvent (X ω) ζ‖ ≤ |ζ.im|⁻¹ := by
    simpa only [specNorm_eq_norm] using hω.specNorm_resolvent_le hζ
  have hs : ‖resolvent (X ω) (star ζ)‖ ≤ |ζ.im|⁻¹ := by
    simpa only [Complex.star_def, Complex.conj_im, abs_neg, specNorm_eq_norm] using
      hω.specNorm_resolvent_le hstar
  have hpow (Y : Matrix n n ℂ) : ‖Y ^ p‖ ≤ ‖Y‖ ^ p := by
    cases p with
    | zero =>
      simpa only [pow_zero, ← specNorm_eq_norm] using
        (specNorm_one_le (n := n) (𝕜 := ℂ))
    | succ k => exact norm_pow_le' Y (Nat.succ_pos k)
  calc
    _ ≤ ‖resolvent (X ω) ζ ^ p * resolvent (X ω) (star ζ) ^ p‖ :=
      by simpa only [specNorm_eq_norm] using
        (norm_normalizedTrace_le_specNorm (resolvent (X ω) ζ ^ p * resolvent (X ω) (star ζ) ^ p))
    _ ≤ ‖resolvent (X ω) ζ‖ ^ p * ‖resolvent (X ω) (star ζ)‖ ^ p :=
      (norm_mul_le _ _).trans (mul_le_mul (hpow _) (hpow _)
        (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    _ ≤ (|ζ.im|⁻¹) ^ p * (|ζ.im|⁻¹) ^ p :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hr p)
        (pow_le_pow_left₀ (norm_nonneg _) hs p)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

open scoped Matrix.Norms.L2Operator in
/-- The genuine expected resolvent Gram moment equals the real part of the actual mixed-resolvent trace integral.
Source: arXiv:2108.06312v2, Theorem 6.2 mixed-moment identity.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem integral_resolventEvenMoment_eq_re_mixed_pow
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) (p : ℕ) :
    (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) =
      (∫ ω, normalizedTrace (resolvent (X ω) ζ ^ p *
        resolvent (X ω) (star ζ) ^ p) ∂μ).re := by
  calc
    _ = ∫ ω, (normalizedTrace (resolvent (X ω) ζ ^ p *
        resolvent (X ω) (star ζ) ^ p)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards [hX] with ω hω
      exact resolventEvenMoment_eq_re_normalizedTrace_mul_pow hω ζ p
    _ = _ := Complex.reCLM.integral_comp_comm
      (integrable_normalizedTrace_resolvent_mixed_pow μ X hXm hX hζ p)

end NLAlib

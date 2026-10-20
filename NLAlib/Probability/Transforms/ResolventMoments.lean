import NLAlib.Matrix.Functions.ResolventMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual expected normalized resolvent moments

Nonreal shifts give integrability and a uniform expectation bound without
moments of the random Hermitian matrix. In positive matrix dimension these
expectations are strictly positive, as required by rooted interpolation.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLAlib

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

/-- Actual normalized positive-order resolvent Gram moments are integrable
and have the uniform imaginary-height expectation bound. Empty matrix shapes
and arbitrary dependence or matrix tails are allowed. -/
theorem integrable_and_integral_resolventEvenMoment_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    Integrable (fun ω => resolventEvenMoment (X ω) ζ p) μ ∧
      (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ≤ (|ζ.im|⁻¹) ^ (2 * p) := by
  have hm := ((measurable_resolventEvenMoment ζ p).comp_aemeasurable hXm).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ‖resolventEvenMoment (X ω) ζ p‖ ≤ (|ζ.im|⁻¹) ^ (2 * p) := by
    filter_upwards [hX] with ω hω
    rw [Real.norm_of_nonneg (resolventEvenMoment_nonneg (X ω) ζ hp)]
    exact resolventEvenMoment_le_inv_abs_im_pow (X ω) hω hζ hp
  refine ⟨Integrable.of_bound hm _ hb, ?_⟩
  exact (le_abs_self _).trans (by simpa [Measure.real] using norm_integral_le_of_norm_le_const hb)

/-- Expected nonreal Hermitian resolvent Gram moments are strictly positive
in nonempty matrix dimension; the law needs no matrix moment assumptions. -/
theorem integral_resolventEvenMoment_pos [Nonempty n]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    0 < ∫ ω, resolventEvenMoment (X ω) ζ p ∂μ := by
  have hi := (integrable_and_integral_resolventEvenMoment_le μ X hXm hX hζ hp).1
  have hPos : ∀ᵐ ω ∂μ, 0 < resolventEvenMoment (X ω) ζ p :=
    hX.mono fun _ hω => hω.resolventEvenMoment_pos hζ hp
  apply (integral_pos_iff_support_of_nonneg_ae (hPos.mono fun _ h => h.le) hi).2
  have hs : Function.support (fun ω => resolventEvenMoment (X ω) ζ p) =ᵐ[μ]
      (Set.univ : Set Ω) := by
    filter_upwards [hPos] with ω hω
    apply propext
    change resolventEvenMoment (X ω) ζ p ≠ 0 ↔ True
    exact iff_true_intro hω.ne'
  rw [measure_congr hs]
  simp

/-- The positive root of an actual expected resolvent Gram moment is at
most the inverse imaginary height. No matrix moment assumptions are needed,
and empty matrix shapes are allowed. -/
theorem integral_resolventEvenMoment_rpow_inv_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^ (1 / ((2 * p : ℕ) : ℝ)) ≤ |ζ.im|⁻¹ := by
  have hnonneg : 0 ≤ ∫ ω, resolventEvenMoment (X ω) ζ p ∂μ :=
    integral_nonneg fun ω => resolventEvenMoment_nonneg (X ω) ζ hp
  have hbound := (integrable_and_integral_resolventEvenMoment_le μ X hXm hX hζ hp).2
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ((|ζ.im|⁻¹) ^ (2 * p)) ^ (1 / ((2 * p : ℕ) : ℝ)) :=
      Real.rpow_le_rpow hnonneg hbound (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, one_div,
        Real.rpow_rpow_inv (inv_nonneg.mpr (abs_nonneg _)) hk.ne']

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Roots of two actual expected Hermitian resolvent moments differ by at
most the inverse imaginary height, on arbitrary probability spaces. -/
theorem abs_integral_resolventEvenMoment_rpow_inv_sub_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : Ω → Matrix n n ℂ) (Y : Ω' → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y ν)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hY : ∀ᵐ ω ∂ν, (Y ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    |(∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^ (1 / ((2 * p : ℕ) : ℝ)) -
      (∫ ω, resolventEvenMoment (Y ω) ζ p ∂ν) ^ (1 / ((2 * p : ℕ) : ℝ))| ≤ |ζ.im|⁻¹ := by
  have hxb := integral_resolventEvenMoment_rpow_inv_le μ X hXm hX hζ hp
  have hyb := integral_resolventEvenMoment_rpow_inv_le ν Y hYm hY hζ hp
  have hxn : 0 ≤ (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^
      (1 / ((2 * p : ℕ) : ℝ)) :=
    Real.rpow_nonneg (integral_nonneg fun ω => resolventEvenMoment_nonneg (X ω) ζ hp) _
  have hyn : 0 ≤ (∫ ω, resolventEvenMoment (Y ω) ζ p ∂ν) ^
      (1 / ((2 * p : ℕ) : ℝ)) :=
    Real.rpow_nonneg (integral_nonneg fun ω => resolventEvenMoment_nonneg (Y ω) ζ hp) _
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end NLAlib

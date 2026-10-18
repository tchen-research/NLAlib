import NLAlib.Matrix.Functions.ResolventMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Expected resolvents of Hermitian random matrices

Nonreal shifts make actual matrix resolvents integrable without any moment
assumption on the random matrix. Their expectations have the same uniform
spectral-norm bound, including empty matrix shapes and singular matrix laws.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLAlib

variable {n Ω Ω' : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- A nonreal resolvent of an almost surely Hermitian measurable random
matrix is integrable, and its actual expectation has spectral norm at most
the inverse absolute imaginary part. No moments of the matrix are required. -/
theorem integrable_and_specNorm_integral_resolvent_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → M)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    Integrable (fun ω => resolvent (X ω) ζ) μ ∧
      specNorm (∫ ω, resolvent (X ω) ζ ∂μ) ≤ |ζ.im|⁻¹ := by
  have hm := ((measurable_matrix_resolvent ζ).comp_aemeasurable hXm).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ‖resolvent (X ω) ζ‖ ≤ |ζ.im|⁻¹ :=
    hX.mono fun ω hω => hω.specNorm_resolvent_le hζ
  refine ⟨Integrable.of_bound hm _ hb, ?_⟩
  simpa [specNorm_eq_norm, Measure.real] using
    norm_integral_le_of_norm_le_const hb

open scoped Matrix.Norms.L2Operator in
/-- Any two actual Hermitian matrix resolvent expectations differ by at most
twice the inverse absolute imaginary part, on arbitrary probability spaces. -/
theorem specNorm_integral_resolvent_sub_integral_resolvent_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : Ω → M) (Y : Ω' → M)
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y ν)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hY : ∀ᵐ ω ∂ν, (Y ω).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    specNorm ((∫ ω, resolvent (X ω) ζ ∂μ) - ∫ ω, resolvent (Y ω) ζ ∂ν) ≤
      2 * |ζ.im|⁻¹ := by
  have hx := (integrable_and_specNorm_integral_resolvent_le μ X hXm hX ζ hζ).2
  have hy := (integrable_and_specNorm_integral_resolvent_le ν Y hYm hY ζ hζ).2
  calc
    _ ≤ specNorm (∫ ω, resolvent (X ω) ζ ∂μ) +
        specNorm (∫ ω, resolvent (Y ω) ζ ∂ν) := norm_sub_le _ _
    _ ≤ |ζ.im|⁻¹ + |ζ.im|⁻¹ := add_le_add hx hy
    _ = _ := (two_mul _).symm

end NLAlib

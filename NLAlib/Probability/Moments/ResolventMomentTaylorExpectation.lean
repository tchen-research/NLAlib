import NLAlib.Matrix.Functions.ResolventMomentTaylor
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrable actual cubic Taylor cancellation under bounded matrix directions

Prerequisite for
`independent-sum-spectrum-universality`. Coordinate-null directions may be
unbounded. All integrability is derived from actual reconstructed matrix
bounds and the genuine continuous native cubic kernel.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Section 6.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- Actual cubic Taylor terms and their cancellation are integrable under
bounded reconstructed directions. Their expectation identity is derived
without any coordinate L3 or supplied remainder bound premise. -/
theorem integrable_and_integral_fderiv_sub_sub_smul_normalizedTrace_mixed_eq_kernel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (a : ℝ)
    (x D V : Ω → E) (hxm : AEMeasurable x μ) (hDm : AEMeasurable D μ)
    (hVm : AEMeasurable V μ) {r : ℝ} (hr : 0 ≤ r)
    (hBound : ∀ᵐ ω ∂μ, specNorm (L (D ω)) ≤ r ∧ specNorm (L (V ω)) ≤ r) :
    let Φ : E → ℂ := fun y => normalizedTrace
      (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
    Integrable (fun ω => resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω)) μ ∧
      Integrable (fun ω => (fderiv ℝ Φ (x ω + a • D ω) - fderiv ℝ Φ (x ω)) (D ω) -
        a • iteratedFDeriv ℝ 2 Φ (x ω - a • V ω) ![D ω, D ω]) μ ∧
      (∫ ω, (fderiv ℝ Φ (x ω + a • D ω) - fderiv ℝ Φ (x ω)) (D ω) -
        a • iteratedFDeriv ℝ 2 Φ (x ω - a • V ω) ![D ω, D ω] ∂μ) =
        a ^ 2 • ∫ ω, resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω) ∂μ := by
  dsimp only
  let Φ : E → ℂ := fun y => normalizedTrace
    (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
  let C : ℝ := 2 * ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    ((2 * p + 2 : ℕ) : ℝ) * (|ζ.im|⁻¹) ^ (2 * p + 3) * r ^ 3
  have hKm : AEStronglyMeasurable
      (fun ω => resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω)) μ := by
    have hc := (continuous_resolventMomentTaylorKernel A hA ζ hζ p a).measurable
    have h := hc.comp_aemeasurable (hxm.prodMk (hDm.prodMk hVm))
    exact h.aestronglyMeasurable
  have hKb : ∀ᵐ ω ∂μ,
      ‖resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω)‖ ≤ C := by
    filter_upwards [hBound] with ω hω
    apply norm_resolventMomentTaylorKernel_le A hA ζ hζ p a (x ω) (D ω) (V ω) hr
    · simpa only [specNorm_eq_norm] using hω.1
    · simpa only [specNorm_eq_norm] using hω.2
  have hKi : Integrable
      (fun ω => resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω)) μ :=
    (integrable_const C).mono' hKm hKb
  have hpoint (ω : Ω) :
      (fderiv ℝ Φ (x ω + a • D ω) - fderiv ℝ Φ (x ω)) (D ω) -
        a • iteratedFDeriv ℝ 2 Φ (x ω - a • V ω) ![D ω, D ω] =
      a ^ 2 • resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω) :=
    fderiv_sub_sub_smul_iteratedFDeriv_two_normalizedTrace_mixed_eq_kernel
      A hA ζ hζ p (x ω) (D ω) (V ω) a
  refine ⟨hKi, (hKi.smul (a ^ 2)).congr (Filter.Eventually.of_forall fun ω => (hpoint ω).symm), ?_⟩
  calc
    _ = ∫ ω, a ^ 2 • resolventMomentTaylorKernel A ζ p a (x ω) (D ω) (V ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_smul _ _

end NLAlib

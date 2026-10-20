import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! # Strict positivity of actual Stieltjes boundary kernels

A nonzero positive measure to the right of a real evaluation point
gives strictly positive value and derivative. Compactness supplies the
native integrability, rather than a formal boundary value assumption.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
namespace MeasureTheory

private theorem stieltjes_integral_pos_of_ae_pos
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ≠0)
    (f : ℝ → ℝ) (hfi : Integrable f μ) (hf : ∀ᵐ ξ ∂μ, 0<f ξ) :
    0<∫ ξ : ℝ, f ξ ∂μ := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  have hn : ∀ᵐ ξ ∂μ, 0≤f ξ := hf.mono fun _ h => h.le
  apply (integral_nonneg_of_ae hn).lt_of_ne'
  intro hzero
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hfi).mp hzero
  obtain ⟨ξ,hξ,hξ0⟩ := (hf.and he).exists
  change f ξ=0 at hξ0
  exact hξ.ne' hξ0

/-- The actual Stieltjes kernel and its actual derivative have strictly
positive real integrals at a point below the support of a nonzero finite
compactly supported measure. This includes atomic measures and does
not assume existence of a density or boundary limit. -/
theorem integral_inv_sub_pos_and_sq_pos_of_support_gt
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    (hμne : μ≠0) (u : ℝ) (hu : ∀ ξ ∈ μ.support, u<ξ) :
    0<∫ ξ : ℝ, (ξ-u)⁻¹ ∂μ ∧ 0<∫ ξ : ℝ, ((ξ-u)⁻¹)^2 ∂μ := by
  have hc : ContinuousOn (fun ξ : ℝ => (ξ-u)⁻¹) μ.support :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      (fun ξ hξ => (sub_pos.mpr (hu ξ hξ)).ne')
  have hre : μ.restrict μ.support=μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  have hi : Integrable (fun ξ : ℝ => (ξ-u)⁻¹) μ := by
    have hh := hc.integrableOn_compact (μ := μ) hμ
    rwa [IntegrableOn,hre] at hh
  have hi2 : Integrable (fun ξ : ℝ => ((ξ-u)⁻¹)^2) μ := by
    have hh := (hc.pow 2).integrableOn_compact (μ := μ) hμ
    rwa [IntegrableOn,hre] at hh
  have hp : ∀ᵐ ξ ∂μ, 0<(ξ-u)⁻¹ := by
    filter_upwards [μ.support_mem_ae] with ξ hξ
    exact inv_pos.mpr (sub_pos.mpr (hu ξ hξ))
  refine ⟨stieltjes_integral_pos_of_ae_pos μ hμne _ hi hp,?_⟩
  exact stieltjes_integral_pos_of_ae_pos μ hμne _ hi2
    (hp.mono fun _ h => sq_pos_of_pos h)

end MeasureTheory

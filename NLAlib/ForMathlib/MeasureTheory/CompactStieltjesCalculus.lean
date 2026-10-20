import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Native complex Stieltjes calculus off a compact real support

The existing real compact-support differentiation theorem supplies the
integral derivative. Its actual derivative is complex-linear, giving a
complex derivative and an analytic continuation off the true support.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace MeasureTheory

/-- A finite compactly supported real measure has the actual complex
Stieltjes derivative at every point separated from its true support.
All integrability and differentiation hypotheses are derived from the
native support, including real evaluation points in spectral gaps. -/
theorem hasDerivAt_integral_real_cauchyKernel_of_support
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    (z : ℂ) (hz : ∀ ξ ∈ μ.support, (ξ : ℂ)≠z) :
    HasDerivAt (fun w : ℂ => ∫ ξ : ℝ, ((ξ : ℂ)-w)⁻¹ ∂μ)
      (∫ ξ : ℝ, (((ξ : ℂ)-z)⁻¹)^2 ∂μ) z := by
  let F : ℂ → ℝ → ℂ := fun w ξ => ((ξ : ℂ)-w)⁻¹
  let D : ℂ → ℝ → ℂ →L[ℝ] ℂ :=
    fun w ξ => ((((ξ : ℂ)-w)⁻¹)^2)•(ContinuousLinearMap.id ℝ ℂ)
  let U : Set (ℂ×ℝ) := {p | (p.2 : ℂ)-p.1≠0}
  have harg : Continuous (fun p : ℂ×ℝ => (p.2 : ℂ)-p.1) := by fun_prop
  have hU : IsOpen U := isOpen_ne_fun harg continuous_const
  have hFi : ContinuousOn (fun p : ℂ×ℝ => F p.1 p.2) U :=
    harg.continuousOn.inv₀ (fun _ hp => hp)
  have hDi : ContinuousOn (fun p : ℂ×ℝ => D p.1 p.2) U :=
    (hFi.pow 2).smul continuousOn_const
  have hd (p : ℂ×ℝ) (hp : p∈U) :
      HasFDerivAt (fun w => F w p.2) (D p.1 p.2) p.1 := by
    have hh : HasDerivAt (fun w : ℂ => ((p.2 : ℂ)-w)⁻¹)
        ((((p.2 : ℂ)-p.1)⁻¹)^2) p.1 := by
      convert! (((hasDerivAt_const p.1 (p.2 : ℂ)).sub (hasDerivAt_id p.1)).inv hp) using 1
      simp only [zero_sub,neg_neg,one_div,inv_pow]
      rfl
    convert! hh.hasFDerivAt.restrictScalars ℝ using 1
    ext w
    simp only [D,ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
      _root_.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    ring
  have hpoint : ∀ ξ ∈ μ.support, (z,ξ)∈U := by
    intro ξ hξ
    exact sub_ne_zero.mpr (hz ξ hξ)
  have h := NLAlib.hasFDerivAt_integral_of_compact_support μ hμ F D U hU hFi hDi hd z hpoint
  have hIntD : Integrable (D z) μ := by
    have hi0 : ContinuousOn (fun ξ : ℝ => ((ξ : ℂ)-z)⁻¹) μ.support :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn.inv₀
        (fun ξ hξ => sub_ne_zero.mpr (hz ξ hξ))
    have hc : ContinuousOn (D z) μ.support := by
      exact (hi0.pow 2).smul continuousOn_const
    have hi := hc.integrableOn_compact (μ := μ) hμ
    have hre : μ.restrict μ.support=μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
    rwa [IntegrableOn,hre] at hi
  have he : (ContinuousLinearMap.toSpanSingleton ℂ
      (∫ ξ : ℝ, (((ξ : ℂ)-z)⁻¹)^2 ∂μ)).restrictScalars ℝ=∫ ξ : ℝ,D z ξ ∂μ := by
    ext w
    rw [ContinuousLinearMap.integral_apply hIntD]
    simp only [D,ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
      _root_.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,integral_mul_const]
    exact mul_comm _ _
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
    (hasFDerivAt_of_restrictScalars ℝ h he).hasDerivAt

/-- The actual scalar Stieltjes integral is analytic on the open
complement of the embedded compact real support. In particular its
continuation across a true real gap is constructed directly. -/
theorem analyticAt_integral_real_cauchyKernel_of_support
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    (z : ℂ) (hz : ∀ ξ ∈ μ.support, (ξ : ℂ)≠z) :
    AnalyticAt ℂ (fun w : ℂ => ∫ ξ : ℝ, ((ξ : ℂ)-w)⁻¹ ∂μ) z := by
  have he : IsClosed (Complex.ofReal '' μ.support) :=
    (hμ.image Complex.continuous_ofReal).isClosed
  have hzmem : z∈(Complex.ofReal '' μ.support)ᶜ := by
    rintro ⟨ξ,hξ,hξz⟩
    exact hz ξ hξ hξz
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [he.isOpen_compl.mem_nhds hzmem] with w hw
  apply (hasDerivAt_integral_real_cauchyKernel_of_support μ hμ w ?_).differentiableAt
  intro ξ hξ hξw
  exact hw ⟨ξ,hξ,hξw⟩

end MeasureTheory

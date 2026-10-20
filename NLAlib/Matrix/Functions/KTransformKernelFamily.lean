import NLAlib.Matrix.Functions.KTransformKernelMeasure
import NLAlib.Matrix.Norms.TraceSpectral

/-! # The actual uniformly finite family of sample-defect measures

The native K equation constructs the sample measures, their compact-law
mass bound, true transform continuity and exact averaged transform.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "Tspace" => selfAdjoint M

/-- The actual sample-defect transform is jointly continuous in the
Hermitian sample and the real part of the upper-half-plane parameter.
This gives genuine product measurability for positive-test inversion;
no measure-valued measurability assertion is supplied. -/
theorem continuous_matrixKResolvent_defect_fixed_height
    (F : ℂ → M) (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hFpos : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef)
    (γ : NNReal) (hγ : γ≠0) :
    Continuous (fun p : Tspace × ℝ => normalizedTrace (p.1.val-
      matrixKResolvent (F ((p.2 : ℂ)+(γ : ℝ)*Complex.I)) p.1.val)) := by
  let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hγpos : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hZ : Continuous (fun p : Tspace × ℝ => (p.2 : ℂ)+(γ : ℝ)*Complex.I) := by fun_prop
  have hT : Continuous (fun p : Tspace × ℝ => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  apply continuous_iff_continuousAt.mpr
  intro p
  have hz : 0<((p.2 : ℂ)+(γ : ℝ)*Complex.I).im := by simpa using hγpos
  have hcF := (hFa _ hz).continuousAt.comp
    (f := fun p : Tspace × ℝ => (p.2 : ℂ)+(γ : ℝ)*Complex.I) hZ.continuousAt
  have harg : ContinuousAt (fun p : Tspace × ℝ =>
      (F ((p.2 : ℂ)+(γ : ℝ)*Complex.I),p.1.val)) p := hcF.prodMk hT.continuousAt
  have hη := (continuousAt_matrixKResolvent (F ((p.2 : ℂ)+(γ : ℝ)*Complex.I)) p.1.val
    (isUnit_matrixKDenominator_of_posDef_imaginaryPart (F _) p.1.val
      (hFpos _ hz) p.1.property)).comp
        (f := fun p : Tspace × ℝ => (F ((p.2 : ℂ)+(γ : ℝ)*Complex.I),p.1.val)) harg
  exact L.continuous.continuousAt.comp (hT.continuousAt.sub hη)

/-- The original compact sample law constructs the actual positive
sample-defect measures with an AE uniform mass bound, continuous native
transforms, and their exact mean identity. The family is chosen from a
proved Herglotz characterization; no measure kernel is assumed.
Source: Montanari--Saeed (2026), native K equation and real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_matrixKResolvent_defect_measure_family
    (ν : Measure Tspace) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1) :
    ∃ ρ : Tspace → FiniteMeasure ℝ, ∃ B : NNReal,
      (∀ T : Tspace, ((ρ T).mass : ℝ)=α⁻¹*(normalizedTrace (T.val*T.val)).re) ∧
      (∀ᵐ T ∂ν, (ρ T).mass≤B) ∧
      (∀ T : Tspace, ∀ z : ℂ, 0<z.im → normalizedTrace
        (T.val-matrixKResolvent (F z) T.val)=
          ∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(ρ T : Measure ℝ)) ∧
      (∀ z : ℂ, 0<z.im → Continuous
        (fun T : Tspace => normalizedTrace (T.val-matrixKResolvent (F z) T.val))) ∧
      ∀ z : ℂ, 0<z.im →
        (∫ T : Tspace, normalizedTrace (T.val-matrixKResolvent (F z) T.val) ∂ν)=
          normalizedTrace ((∫ T : Tspace, T.val ∂ν)-z•1-α⁻¹•(F z)⁻¹) := by
  classical
  have hs (T : Tspace) :=
    (existsUnique_stieltjes_measure_matrixKResolvent_defect ν hν α hα F hFa hF T.val T.property).exists
  choose ρ hρ using hs
  obtain ⟨R0,hR0⟩ := hν.isBounded.exists_norm_le
  let R := max R0 0
  have hR : 0≤R := le_max_right _ _
  let B : NNReal := ⟨α⁻¹*R^2,by positivity⟩
  have hmass : ∀ᵐ T ∂ν, (ρ T).mass≤B := by
    filter_upwards [ν.support_mem_ae] with T hT
    apply NNReal.coe_le_coe.mp
    rw [(hρ T).1]
    have hTN : ‖T.val‖≤R := by
      have hh := (hR0 T hT).trans (le_max_left R0 0)
      simpa only [← AddSubgroup.norm_coe] using hh
    have hsq : (normalizedTrace (T.val*T.val)).re≤R^2 := by
      calc
        _ ≤ ‖normalizedTrace (T.val*T.val)‖ := Complex.re_le_norm _
        _ ≤ ‖T.val*T.val‖ := by
          simpa only [specNorm_eq_norm] using norm_normalizedTrace_le_specNorm (T.val*T.val)
        _ ≤ ‖T.val‖*‖T.val‖ := norm_mul_le _ _
        _ ≤ R^2 := by simpa only [sq] using mul_self_le_mul_self (norm_nonneg T.val) hTN
    exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hα.le)
  have hcont (z : ℂ) (hz : 0<z.im) : Continuous
      (fun T : Tspace => normalizedTrace (T.val-matrixKResolvent (F z) T.val)) := by
    let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
    have hc : Continuous (fun T : Tspace => matrixKResolvent (F z) T.val) := by
      apply continuous_iff_continuousAt.mpr
      intro T
      exact (continuousAt_matrixKResolvent (F z) T.val
        (isUnit_matrixKDenominator_of_posDef_imaginaryPart (F z) T.val (hF z hz).1 T.property)).comp
          (f := fun T : Tspace => (F z,T.val))
          (continuous_const.prodMk continuous_subtype_val).continuousAt
    exact L.continuous.comp (continuous_subtype_val.sub hc)
  refine ⟨ρ,B,fun T => (hρ T).1,hmass,fun T => (hρ T).2,hcont,?_⟩
  intro z hz
  have hdom : F z∈matrixKTransformDomain ν :=
    ⟨Matrix.isUnit_of_posDef_imaginaryPart (hF z hz).1,fun T _ =>
      isUnit_matrixKDenominator_of_posDef_imaginaryPart (F z) T.val (hF z hz).1 T.property⟩
  have hη := integrable_matrixKResolvent_of_mem_domain ν hν hdom
  have hT : Integrable (fun T : Tspace => T.val) ν := by
    have hi := continuous_subtype_val.continuousOn.integrableOn_compact (μ := ν) hν
    have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
    rwa [IntegrableOn,hre] at hi
  let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hmean : (∫ T : Tspace, T.val-matrixKResolvent (F z) T.val ∂ν)=
      (∫ T : Tspace, T.val ∂ν)-z•1-α⁻¹•(F z)⁻¹ := by
    have hK := (hF z hz).2
    unfold matrixKTransform at hK
    rw [integral_sub hT hη,sub_eq_iff_eq_add.mp hK]
    abel
  have hh := L.integral_comp_comm (hT.sub hη)
  simp only [Pi.sub_apply] at hh
  change (∫ T : Tspace, L (T.val-matrixKResolvent (F z) T.val) ∂ν)=L _
  rw [hh,hmean]

end NLAlib

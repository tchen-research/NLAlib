import NLAlib.Matrix.Functions.KTransformKernelFamily
import NLAlib.Matrix.Functions.KTransformRealStieltjesBranch
import NLAlib.ForMathlib.Analysis.Matrix.HermitianBoundaryBound
import NLAlib.ForMathlib.MeasureTheory.StieltjesFamilyBound
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral

/-! # Native sample-defect bounds in a true trace-law gap

The original nonlinear K equation gives the exact averaged transform.
The constructed real Stieltjes branch makes that average O(height).
Positive-test inversion then bounds every actual sample transform.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter Metric
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "Tspace" => selfAdjoint M

/-- Below the actual normalized-trace law, every sample in the true
compact ν-support has a uniformly bounded native defect transform.
The sample representing measures, averaged boundary estimate, compact
positive test and supportwise bound are constructed from the original
nonlinear K equation. No sample denominator gap or boundary bound is
assumed.
Source: Montanari--Saeed (2026), Theorem 3, real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_uniform_matrixKResolvent_defect_bound_below_trace_support
    (ν : Measure Tspace) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u<t) :
    ∃ B : ℝ, 0≤B ∧ ∀ T ∈ ν.support, ∀ z : ℂ, 0<z.im → z.re=u →
      ‖normalizedTrace (T.val-matrixKResolvent (F z) T.val)‖≤B := by
  obtain ⟨G,hGa,hGN,hreal,hGpos,_hGderiv⟩ :=
    exists_posDef_real_stieltjes_extension_matrixKTransform ν hν α hα F hFa hF μ hμ u hu
  let S : ℂ → M := fun z => α⁻¹•G z
  let Q : ℂ → M := fun z => (S z)⁻¹
  have hSpos : (S u).PosDef := hGpos.smul (inv_pos.mpr hα)
  have hSa : AnalyticAt ℂ S (u : ℂ) := hGa.const_smul (c := α⁻¹)
  have hQa : AnalyticAt ℂ Q (u : ℂ) := by
    have hh := analyticAt_inverse (𝕜 := ℂ) hSpos.isUnit.unit
    rw [hSpos.isUnit.unit_spec] at hh
    simpa only [Q,Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse] using hh.comp (f := S) hSa
  have hQreal : ∀ x : ℝ, (Q x).IsHermitian :=
    fun x => ((hreal x).smul (IsSelfAdjoint.all α⁻¹)).inv
  have hQupper (z : ℂ) (hz : 0<z.im) : Q z=(F z)⁻¹ := by
    simp only [Q,S,hGN z hz,smul_smul,inv_mul_cancel₀ hα.ne',one_smul]
  obtain ⟨C,hC,hQbound⟩ := Matrix.exists_eventually_norm_imaginaryPart_le_height_of_real_analytic
    Q u hQa (Eventually.of_forall hQreal)
  obtain ⟨η,hη,hηbound⟩ := Metric.mem_nhds_iff.mp hQbound
  let ε := η/4
  have hε : 0<ε := div_pos hη (by norm_num)
  obtain ⟨ρ,B,_hmassExact,hmass,hrep,hcont,hmean⟩ :=
    exists_matrixKResolvent_defect_measure_family ν hν α hα F hFa hF
  have hET : (∫ T : Tspace, T.val ∂ν).IsHermitian :=
    Matrix.isHermitian_integral (Eventually.of_forall fun T => T.property)
  have havg : ∀ x ∈ ball u ε, ∀ γ : NNReal, γ≠0 → (γ : ℝ)<ε →
      (∫ T : Tspace,
        (normalizedTrace (T.val-matrixKResolvent (F ((x : ℂ)+(γ : ℝ)*Complex.I)) T.val)).im ∂ν)≤
          (1+α⁻¹*C)*(γ : ℝ) := by
    intro x hx γ hγ hsmall
    have hγpos : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
    let z : ℂ := (x : ℂ)+(γ : ℝ)*Complex.I
    have hz : 0<z.im := by simpa [z] using hγpos
    have hzγ : z.im=(γ : ℝ) := by simp [z]
    have hxu : |x-u|<ε := by simpa only [mem_ball,Real.dist_eq] using hx
    have hdist : dist z (u : ℂ)<η := by
      rw [dist_eq_norm]
      have he : z-(u : ℂ)=((x-u : ℝ) : ℂ)+(γ : ℝ)*Complex.I := by
        dsimp only [z]
        push_cast
        ring
      rw [he]
      have hn := norm_add_le (((x-u : ℝ) : ℂ)) (((γ : ℝ) : ℂ)*Complex.I)
      rw [norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_I,mul_one,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hγpos] at hn
      dsimp only [ε] at *
      exact hn.trans_lt (by linarith)
    have hQnorm : ‖(imaginaryPart (Q z) : M)‖≤C*(γ : ℝ) := by
      simpa only [hzγ] using hηbound hdist hz
    have hi : Integrable
        (fun T : Tspace => normalizedTrace (T.val-matrixKResolvent (F z) T.val)) ν := by
      have hh := (hcont z hz).continuousOn.integrableOn_compact (μ := ν) hν
      have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
      rwa [IntegrableOn,hre] at hh
    have him : (∫ T : Tspace, normalizedTrace (T.val-matrixKResolvent (F z) T.val) ∂ν).im=
        ∫ T : Tspace, (normalizedTrace (T.val-matrixKResolvent (F z) T.val)).im ∂ν :=
      (integral_im hi).symm
    change (∫ T : Tspace, (normalizedTrace (T.val-matrixKResolvent (F z) T.val)).im ∂ν)≤_
    rw [← him,hmean z hz,← hQupper z hz]
    let A : M := (∫ T : Tspace, T.val ∂ν)-z•1-α⁻¹•Q z
    have hImScalar : (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
      have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
      simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]
    have hImScale : (imaginaryPart (α⁻¹•Q z) : M)=α⁻¹•(imaginaryPart (Q z) : M) := by
      rw [map_smul]
      rfl
    have hAI : (imaginaryPart A : M)= -((γ : ℝ)•(1 : M))-α⁻¹•(imaginaryPart (Q z) : M) := by
      dsimp only [A]
      rw [map_sub,map_sub,hET.isSelfAdjoint.imaginaryPart]
      simp only [zero_sub,NegMemClass.coe_neg,AddSubgroup.coe_sub]
      rw [hImScalar,hImScale,hzγ]
    have hnorm : ‖(imaginaryPart A : M)‖≤(1+α⁻¹*C)*(γ : ℝ) := by
      rw [hAI]
      calc
        _ ≤ ‖-((γ : ℝ)•(1 : M))‖+‖α⁻¹•(imaginaryPart (Q z) : M)‖ := norm_sub_le _ _
        _ = (γ : ℝ)+α⁻¹*‖(imaginaryPart (Q z) : M)‖ := by
          rw [norm_neg,norm_smul,norm_smul,Real.norm_of_nonneg hγpos.le,
            Real.norm_of_nonneg (inv_nonneg.mpr hα.le),norm_one,mul_one]
        _ ≤ (γ : ℝ)+α⁻¹*(C*(γ : ℝ)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hQnorm (inv_nonneg.mpr hα.le))
        _ = _ := by ring
    have htrace : (normalizedTrace A).im≤‖(imaginaryPart A : M)‖ := by
      simpa only [specNorm_eq_norm] using im_normalizedTrace_le_specNorm_imaginaryPart A
    exact htrace.trans hnorm
  have hmeas (γ : NNReal) (hγ : γ≠0) : AEStronglyMeasurable
      (fun p : Tspace × ℝ => (normalizedTrace (p.1.val-
        matrixKResolvent (F ((p.2 : ℂ)+(γ : ℝ)*Complex.I)) p.1.val)).im) (ν.prod volume) :=
    (Complex.continuous_im.comp (continuous_matrixKResolvent_defect_fixed_height
      F hFa (fun z hz => (hF z hz).1) γ hγ)).aestronglyMeasurable
  exact exists_uniform_stieltjes_bound_on_support_of_local_average_im_bound ν ρ
    (fun T z => normalizedTrace (T.val-matrixKResolvent (F z) T.val)) hrep hcont B hmass hmeas
      u ε ε (1+α⁻¹*C) hε hε havg

end NLAlib

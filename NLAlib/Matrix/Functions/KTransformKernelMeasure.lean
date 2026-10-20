import NLAlib.Matrix.Functions.KTransformStieltjesLaw
import Mathlib.Analysis.Analytic.Constructions

/-! # Actual positive measures of the native sample resolvent defects

Each true sample defect T−η(F(z),T) is a positive-imaginary analytic
function. Its exact normalization constructs a positive scalar measure,
including singular and indefinite samples and the zero-mass case.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

omit [Nonempty n] in
private theorem kernelMeasure_defect_eq (S T : M) (hu : IsUnit (1+S*T)) :
    T-matrixKResolvent S T=T*(1+S*T)⁻¹*S*T := by
  have hcan : (1+S*T)⁻¹*(1+S*T)=1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : T*(1+S*T)⁻¹*(S*T)=T-T*(1+S*T)⁻¹ := by
    have hh := congrArg (fun X : M => T*X) hcan
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [Matrix.mul_add,Matrix.mul_one,Matrix.mul_assoc,add_comm] using hh)
  simpa only [matrixKResolvent,Matrix.mul_assoc] using he.symm

omit [Nonempty n] [DecidableEq n] in
private theorem kernelMeasure_trace_sq (T : M) (hT : T.IsHermitian) :
    0≤(normalizedTrace (T*T)).re ∧
      normalizedTrace (T*T)=((normalizedTrace (T*T)).re : ℂ) := by
  have hp : (T*T).PosSemidef := by
    simpa only [hT.eq] using Matrix.posSemidef_conjTranspose_mul_self T
  have ht := Complex.nonneg_iff.mp hp.trace_nonneg
  have hd : (Fintype.card n : ℂ)⁻¹=(((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv,Complex.ofReal_natCast]
  have he : normalizedTrace (T*T)=
      (((Fintype.card n : ℝ)⁻¹*(T*T).trace.re : ℝ) : ℂ) := by
    rw [normalizedTrace,hd]
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,add_zero,sub_zero,ht.2.symm]
  rw [he]
  simp only [Complex.ofReal_re]
  exact ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ht.1,trivial⟩

omit [Nonempty n] in
private theorem kernelMeasure_tendsto_zero
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1) :
    Tendsto (fun y : ℝ => F ((y : ℂ)*Complex.I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hα tendsto_id))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hz : 0<((y : ℂ)*Complex.I).im := by simpa using hy
  have hZ : (α*y)•(1 : M)≤α•(imaginaryPart (((y : ℂ)*Complex.I)•(1 : M)) : M) := by
    have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
    simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one,smul_smul]
  simpa only [specNorm_eq_norm,Function.comp_def,id_eq] using specNorm_of_matrixKTransform_solution_le_inv ν hν α hα
    (((y : ℂ)*Complex.I)•1) (F _) (hF _ hz).1 (hF _ hz).2 (α*y) (mul_pos hα hy) hZ

omit [Nonempty n] in
/-- Every genuine Hermitian sample has an actual positive finite
Stieltjes measure for its native resolvent defect. The mass is derived
from T² and the true branch normalization. No sample positivity,
invertibility, representing measure, or support conclusion is assumed.
Source: Montanari--Saeed (2026), native kernel (8), analytic real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem existsUnique_stieltjes_measure_matrixKResolvent_defect
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (T : M) (hT : T.IsHermitian) :
    ∃! ρ : FiniteMeasure ℝ,
      (ρ.mass : ℝ)=α⁻¹*(normalizedTrace (T*T)).re ∧
      ∀ z : ℂ, 0<z.im → normalizedTrace (T-matrixKResolvent (F z) T)=
        ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(ρ : Measure ℝ) := by
  let Dfn : ℂ → M := fun z => T-matrixKResolvent (F z) T
  let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  let f : ℂ → ℂ := fun z => L (Dfn z)
  have hunit (z : ℂ) (hz : 0<z.im) : IsUnit (1+F z*T) :=
    isUnit_matrixKDenominator_of_posDef_imaginaryPart (F z) T (hF z hz).1 hT
  have hNa : AnalyticOnNhd ℂ Dfn {z : ℂ | 0<z.im} := by
    intro z hz
    have hden : AnalyticAt ℂ (fun w : ℂ => 1+F w*T) z :=
      analyticAt_const.add ((hFa z hz).mul analyticAt_const)
    have hi : AnalyticAt ℂ (fun w : ℂ => Ring.inverse (1+F w*T)) z := by
      have hh := analyticAt_inverse (𝕜 := ℂ) (hunit z hz).unit
      rw [(hunit z hz).unit_spec] at hh
      exact hh.comp (f := fun w : ℂ => 1+F w*T) hden
    have hi' : AnalyticAt ℂ (fun w : ℂ => (1+F w*T)⁻¹) z := by
      simpa only [Matrix.nonsing_inv_eq_ringInverse] using hi
    exact analyticAt_const.sub (analyticAt_const.mul hi')
  have hfa : AnalyticOnNhd ℂ f {z : ℂ | 0<z.im} :=
    fun z hz => (L.analyticAt (Dfn z)).comp (hNa z hz)
  have hpos : ∀ z : ℂ, 0<z.im → 0≤(f z).im := by
    intro z hz
    have he : (imaginaryPart (Dfn z) : M)=
        matrixKResolvent (F z) T*(imaginaryPart (F z) : M)*(matrixKResolvent (F z) T)ᴴ := by
      dsimp only [Dfn]
      rw [map_sub,hT.isSelfAdjoint.imaginaryPart,zero_sub]
      simp only [NegMemClass.coe_neg,
        imaginaryPart_matrixKResolvent (F z) T (hF z hz).1 hT,neg_neg]
    have hp : (imaginaryPart (Dfn z) : M).PosSemidef := by
      rw [he]
      exact (hF z hz).1.posSemidef.mul_mul_conjTranspose_same _
    exact im_normalizedTrace_nonneg_of_posSemidef_imaginaryPart (Dfn z) hp
  have hFzero := kernelMeasure_tendsto_zero ν hν α hα F hF
  have hdenlim : Tendsto (fun y : ℝ => 1+F ((y : ℂ)*Complex.I)*T) atTop (𝓝 (1 : M)) := by
    simpa only [Matrix.zero_mul,add_zero] using tendsto_const_nhds.add (hFzero.mul_const T)
  have hInvlim : Tendsto (fun y : ℝ => (1+F ((y : ℂ)*Complex.I)*T)⁻¹) atTop (𝓝 (1 : M)) := by
    simpa only [inv_one,Function.comp_def] using
      (hasFDerivAt_matrixInverse (1 : M) isUnit_one).continuousAt.tendsto.comp hdenlim
  have hscale : Tendsto (fun y : ℝ => ((y : ℂ)*Complex.I)•F ((y : ℂ)*Complex.I))
      atTop (𝓝 (-(α⁻¹•(1 : M)))) := by
    have hh := (tendsto_mul_I_smul_matrixKTransform_solution ν hν α hα F hF).const_smul (α⁻¹)
    simpa only [smul_comm α⁻¹,smul_smul,inv_mul_cancel₀ hα.ne',mul_inv_cancel₀ hα.ne',one_smul,smul_neg] using hh
  have hNlim : Tendsto (fun y : ℝ => ((y : ℂ)*Complex.I)•Dfn ((y : ℂ)*Complex.I))
      atTop (𝓝 (-(α⁻¹•(T*T)))) := by
    have hh := ((hInvlim.const_mul T).mul hscale).mul_const T
    have he : T*(1 : M)*(-(α⁻¹•(1 : M)))*T= -(α⁻¹•(T*T)) := by
      simp only [Matrix.mul_one,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_smul,
        Matrix.smul_mul,Matrix.mul_one]
    rw [he] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hz : 0<((y : ℂ)*Complex.I).im := by simpa using hy
    dsimp only [Dfn]
    rw [kernelMeasure_defect_eq (F _) T (hunit _ hz)]
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
  obtain ⟨htr,htrReal⟩ := kernelMeasure_trace_sq T hT
  let c : NNReal := ⟨α⁻¹*(normalizedTrace (T*T)).re,mul_nonneg (inv_nonneg.mpr hα.le) htr⟩
  have hflim : Tendsto (fun y : ℝ => (y : ℂ)*Complex.I*f ((y : ℂ)*Complex.I))
      atTop (𝓝 (-(c : ℝ) : ℂ)) := by
    have hh := (L.continuous.tendsto (-(α⁻¹•(T*T)))).comp hNlim
    have he : L (-(α⁻¹•(T*T)))= (-(c : ℝ) : ℂ) := by
      have hscaleTrace : L (α⁻¹•(T*T))=((α⁻¹ : ℝ) : ℂ)*normalizedTrace (T*T) := by
        simpa only [Complex.real_smul,L,ContinuousLinearMap.coe_restrictScalars',
          LinearMap.coe_toContinuousLinearMap',normalizedTraceLinearMap_apply] using
          map_smul (L.restrictScalars ℝ) (α⁻¹) (T*T)
      rw [map_neg,hscaleTrace]
      calc
        _ = -(((α⁻¹ : ℝ) : ℂ)*((normalizedTrace (T*T)).re : ℂ)) :=
          congrArg (fun w : ℂ => -(((α⁻¹ : ℝ) : ℂ)*w)) htrReal
        _ = _ := by change _ = -((α⁻¹*(normalizedTrace (T*T)).re : ℝ) : ℂ); rw [Complex.ofReal_mul]
    rw [he] at hh
    simpa only [Function.comp_def,map_smul,smul_eq_mul] using hh
  obtain ⟨ρ,hρ,huniq⟩ := hfa.existsUnique_finiteMeasure_stieltjes_eq hpos c hflim
  refine ⟨ρ,⟨congrArg (fun r : NNReal => (r : ℝ)) hρ.1,hρ.2⟩,?_⟩
  intro σ hσ
  apply huniq σ
  refine ⟨?_,hσ.2⟩
  apply NNReal.coe_injective
  exact hσ.1

end NLAlib

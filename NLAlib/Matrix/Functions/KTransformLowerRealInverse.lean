import NLAlib.Matrix.Functions.KTransformRealSampleGaps

/-! # Actual stable scalar inverses throughout the lower trace gap

Boundary continuity recovers the true K equation on the constructed
Stieltjes continuation. Its strictly positive real derivative maps to
the identity under the genuine K derivative, which yields the source
strict stability test rather than assuming it.
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
/-- A genuine regular Stieltjes boundary value satisfies the actual
nonlinear K equation. The conclusion follows from upper-plane values
and native continuity at the solved sample denominators; no real K
equation is assumed.
Source: Montanari--Saeed (2026), Theorem 3, real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_real_stieltjes_extension_eq
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → matrixKTransform ν α (F z)=z•1)
    (G : ℂ → M) (u : ℝ) (hGa : AnalyticAt ℂ G (u : ℂ))
    (hGN : ∀ z : ℂ, 0<z.im → G z=α•F z)
    (hGpos : (G u).PosDef)
    (hgap : ∀ T ∈ ν.support, ((α⁻¹•G u)⁻¹+T.val).PosDef) :
    matrixKTransform ν α (α⁻¹•G u)=(u : ℂ)•1 := by
  let S : ℂ → M := fun z => α⁻¹•G z
  have hSp : (S u).PosDef := hGpos.smul (inv_pos.mpr hα)
  have hdom : S u∈matrixKTransformDomain ν :=
    ⟨hSp.isUnit,fun T hT => isUnit_matrixKDenominator (S u) T.val hSp (hgap T hT)⟩
  let φ : ℝ → ℂ := fun y => (u : ℂ)+(y : ℂ)*Complex.I
  have hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (u : ℂ)) := by
    have hc : Continuous φ := by fun_prop
    simpa only [φ,Complex.ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hSc : ContinuousAt S (u : ℂ) := (hGa.const_smul (c := α⁻¹)).continuousAt
  have hKlim := ((hasFDerivAt_matrixKTransform_complex ν hν α hdom).continuousAt.tendsto.comp
    (hSc.tendsto.comp hφ))
  have htarget : Tendsto (fun y : ℝ => (φ y)•(1 : M)) (𝓝[>] 0) (𝓝 ((u : ℂ)•1)) :=
    hφ.smul_const (1 : M)
  have he : (fun y : ℝ => matrixKTransform ν α (S (φ y))) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => (φ y)•(1 : M)) := by
    filter_upwards [self_mem_nhdsWithin] with y hyp
    have hz : 0<(φ y).im := by simpa [φ] using (show 0<y from hyp)
    have hs : S (φ y)=F (φ y) := by
      simp only [S,hGN _ hz,smul_smul,inv_mul_cancel₀ hα.ne',one_smul]
    rw [hs,hF _ hz]
  exact tendsto_nhds_unique hKlim (htarget.congr' (he.mono fun y hy => hy.symm))

/-- Every real point below the actual characterized trace law has a
true stable scalar K inverse. The sample gaps come from positive
defect measures, the real equation from native continuity, and the
strict stability witness from the positive Stieltjes derivative.
Source: Montanari--Saeed (2026), Theorem 3, lower real component.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_stable_matrixKTransform_scalar_solution_below_trace_support
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass=1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u<t) :
    ∃ S : M, S∈matrixKStableDomain ν α ∧ matrixKTransform ν α S=(u : ℂ)•1 := by
  obtain ⟨G,hGN,_hreal,hGu⟩ :=
    exists_posDef_sample_gap_real_stieltjes_extension_matrixKTransform ν hν α hα F hFa hF
      μ hmass hcompact hμ
  let S : ℂ → M := fun z => α⁻¹•G z
  have hK (x : ℝ) (hx : ∀ t ∈ (μ : Measure ℝ).support, x<t) :
      matrixKTransform ν α (S x)=(x : ℂ)•1 :=
    matrixKTransform_real_stieltjes_extension_eq ν hν α hα F (fun z hz => (hF z hz).2)
      G x (hGu x hx).1 hGN (hGu x hx).2.1 (hGu x hx).2.2.2
  have hG := hGu u hu
  have hSp : (S u).PosDef := hG.2.1.smul (inv_pos.mpr hα)
  have hgap : ∀ T ∈ ν.support, ((S u)⁻¹+T.val).PosDef := hG.2.2.2
  let B : M := α⁻¹•deriv G (u : ℂ)
  have hB : B.PosDef := hG.2.2.1.smul (inv_pos.mpr hα)
  have hSd : HasDerivAt S B (u : ℂ) := hG.1.differentiableAt.hasDerivAt.const_smul α⁻¹
  have hcoe : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
  have hSC : HasFDerivAt S
      ((ContinuousLinearMap.toSpanSingleton ℂ B).restrictScalars ℝ) (u : ℂ) :=
    hSd.hasFDerivAt.restrictScalars ℝ
  have hSdR : HasDerivAt (fun t : ℝ => S (t : ℂ)) B u := by
    convert! hSC.comp_hasDerivAt u hcoe using 1
    simp only [ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  have hchain := (hasFDerivAt_matrixKTransform ν hν α (S u) hSp.isUnit
    (fun T hT => isUnit_matrixKDenominator (S u) T.val hSp (hgap T hT))).comp_hasDerivAt u hSdR
  have hne : (μ : Measure ℝ)≠0 := by
    intro hz
    have hm : μ.mass=0 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass,hz]
      simp
    rw [hmass] at hm
    exact one_ne_zero hm
  let a : ℝ := sInf (μ : Measure ℝ).support
  have ha : a∈(μ : Measure ℝ).support := hcompact.sInf_mem (Measure.nonempty_support hne)
  have hua : u<a := hu a ha
  have he : (fun t : ℝ => matrixKTransform ν α (S (t : ℂ))) =ᶠ[𝓝 u]
      (fun t : ℝ => (t : ℂ)•(1 : M)) := by
    filter_upwards [isOpen_Iio.mem_nhds hua] with x hx
    exact hK x (fun t ht => lt_of_lt_of_le hx (csInf_le hcompact.bddBelow ht))
  have htarget : HasDerivAt (fun t : ℝ => (t : ℂ)•(1 : M)) 1 u := by
    simpa only [one_smul] using hcoe.smul_const (1 : M)
  have hD : matrixKTransformDeriv ν α (S u) B=1 :=
    hchain.unique (htarget.congr_of_eventuallyEq he)
  have hw : ∃ B : M, B.PosDef ∧ (matrixKTransformDeriv ν α (S u) B).PosDef :=
    ⟨B,hB,by rw [hD]; exact Matrix.PosDef.one⟩
  have hstable : S u∈matrixKStableDomain ν α := by
    refine ⟨hSp,hgap,?_⟩
    rw [matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα (S u) hSp hgap,
      matrixKTransform_norm_iff_supersolution ν hν α hα (S u) hSp hgap,
      matrixKTransform_supersolution_iff_derivative_witness ν hν α hα (S u) hSp hgap]
    exact hw
  exact ⟨S u,hstable,hK u hu⟩

end NLAlib

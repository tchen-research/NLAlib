import NLAlib.Matrix.Functions.KTransformHalfPlaneDual
import NLAlib.Matrix.Functions.KTransformGlobalInjectivity
import NLAlib.Matrix.Functions.KTransformLocalInverse

/-! # Upper-half-plane uniqueness for the actual nonlinear K equation

The original and dual native imaginary identities give two strict row
defects. The true two-point K identity then produces a mixed-kernel fixed
point, which must vanish. Source: Montanari--Saeed (2026), the uniqueness
part of Lemma 1, proved in Appendix A using Lemmas 10--13.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem integrable_continuous_compact_support
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    {f : selfAdjoint M → M} (hf : Continuous f) : Integrable f ν := by
  have hi := hf.continuousOn.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

private theorem continuous_kResolvent_upper (S : M) (hS : (imaginaryPart S : M).PosDef) :
    Continuous (fun T : selfAdjoint M => matrixKResolvent S T.val) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (continuousAt_matrixKResolvent S T.val
    (isUnit_matrixKDenominator_of_posDef_imaginaryPart S T.val hS T.property)).comp
      (f := fun T : selfAdjoint M => (S,T.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt

private def upperRowKernel (α : ℝ) (P B U : M) : M :=
  Real.sqrt α • (cfc (fun x => (Real.sqrt x)⁻¹) B*P*U*cfc Real.sqrt B)

private theorem upperRowKernel_gram (α : ℝ) (hα : 0≤α) (P B U : M) (hB : B.PosDef) :
    upperRowKernel α P B U*(upperRowKernel α P B U)ᴴ =
      α • ((cfc (fun x => (Real.sqrt x)⁻¹) B*P)*(U*B*Uᴴ)*
        (cfc (fun x => (Real.sqrt x)⁻¹) B*P)ᴴ) := by
  have hR : (cfc (fun x => (Real.sqrt x)⁻¹) B).IsHermitian := cfc_predicate _ _
  have hQ : (cfc Real.sqrt B).IsHermitian := cfc_predicate _ _
  simp only [upperRowKernel,Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_mul,
    hR.eq,hQ.eq,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Real.mul_self_sqrt hα]
  congr 1
  simpa only [Matrix.mul_assoc] using congrArg
    (fun X => cfc (fun x => (Real.sqrt x)⁻¹) B*P*U*X*Uᴴ*Pᴴ*
      cfc (fun x => (Real.sqrt x)⁻¹) B) (cfc_sqrt_mul_self hB)

private theorem upperRowKernel_defect
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (P B H : M) (hP : IsUnit P) (hB : B.PosDef) (hH : H.PosDef)
    (U : selfAdjoint M → M) (hU : Continuous U)
    (hidentity : H=α⁻¹ • (P⁻¹*B*P⁻¹ᴴ)-∫ T,U T*B*(U T)ᴴ ∂ν) :
    (1-∫ T,upperRowKernel α P B (U T)*(upperRowKernel α P B (U T))ᴴ ∂ν).PosDef := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) B
  let L := R*P
  let f (T : selfAdjoint M) := U T*B*(U T)ᴴ
  have hR : R.IsHermitian := cfc_predicate _ _
  have hi : Integrable f ν := integrable_continuous_compact_support ν hν (by
    dsimp only [f]; fun_prop)
  have he : (∫ T,upperRowKernel α P B (U T)*(upperRowKernel α P B (U T))ᴴ ∂ν) =
      α • (L*(∫ T,f T ∂ν)*Lᴴ) := by
    calc
      _ = ∫ T,α • (L*f T*Lᴴ) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun T => upperRowKernel_gram α hα.le P B (U T) hB
      _ = _ := by
        rw [integral_smul]
        congr 1
        exact (ContinuousLinearMap.mulLeftRight ℝ M L Lᴴ).integral_comp_comm hi
  have hbase : α • (L*(α⁻¹ • (P⁻¹*B*P⁻¹ᴴ))*Lᴴ)=1 := by
    have hb : R*B*R=1 := by
      rw [← cfc_sqrt_mul_self hB]
      change R*(cfc Real.sqrt B*cfc Real.sqrt B)*R=1
      rw [← Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hB,Matrix.one_mul,cfc_sqrt_mul_inv_sqrt hB]
    have hPstar : IsUnit Pᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hP.star
    simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hα.ne',one_smul,
      L,Matrix.conjTranspose_mul,hR.eq,Matrix.conjTranspose_nonsing_inv]
    calc
      _ = R*(P*P⁻¹)*B*((Pᴴ)⁻¹*Pᴴ)*R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP),
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hPstar)]
        simpa only [Matrix.mul_one,Matrix.one_mul] using hb
  have heq : (1-∫ T,upperRowKernel α P B (U T)*(upperRowKernel α P B (U T))ᴴ ∂ν) =
      α • (L*H*Lᴴ) := by
    rw [he,hidentity,Matrix.mul_sub,Matrix.sub_mul,smul_sub,hbase]
  rw [heq]
  apply (posDef_real_smul_iff α hα _).mpr
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    ((isUnit_cfc_invSqrt B hB).mul hP)).mpr hH

private theorem upperRowKernel_mixed
    (α : ℝ) (hα : 0≤α) (S Q B C U V Δ : M) (hB : B.PosDef) (hC : C.PosDef) :
    upperRowKernel α S B U*
        (cfc (fun x => (Real.sqrt x)⁻¹) B*Δ*cfc (fun x => (Real.sqrt x)⁻¹) C)*
          (upperRowKernel α Qᴴ C Vᴴ)ᴴ =
      α • ((cfc (fun x => (Real.sqrt x)⁻¹) B*S)*(U*Δ*V)*
        (Q*cfc (fun x => (Real.sqrt x)⁻¹) C)) := by
  have hR : (cfc (fun x => (Real.sqrt x)⁻¹) C).IsHermitian := cfc_predicate _ _
  have hQ : (cfc Real.sqrt C).IsHermitian := cfc_predicate _ _
  simp only [upperRowKernel,Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,hR.eq,hQ.eq,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Real.mul_self_sqrt hα]
  congr 1
  calc
    _ = cfc (fun x => (Real.sqrt x)⁻¹) B*S*U*
        (cfc Real.sqrt B*cfc (fun x => (Real.sqrt x)⁻¹) B)*Δ*
        (cfc (fun x => (Real.sqrt x)⁻¹) C*cfc Real.sqrt C)*V*Q*
        cfc (fun x => (Real.sqrt x)⁻¹) C := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [cfc_sqrt_mul_inv_sqrt hB,cfc_inv_sqrt_mul_sqrt hC]
      simp only [Matrix.mul_one,Matrix.mul_assoc]

/-- The genuine nonlinear K equation has at most one solution in the
matrix upper half-plane for a given upper-half-plane target. Both strict
mixed-kernel defects are derived from the native original and dual
imaginary-part identities. The compact law may contain singular or
indefinite Hermitian samples; no distinguished branch, Stieltjes law or
contraction conclusion is supplied as a hypothesis.
Source: Montanari--Saeed (2026), Lemma 1, uniqueness part; Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_solution_unique_upperHalfPlane
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z S Q : M)
    (hZ : (imaginaryPart Z : M).PosDef)
    (hS : (imaginaryPart S : M).PosDef) (hQ : (imaginaryPart Q : M).PosDef)
    (hKS : matrixKTransform ν α S=Z) (hKQ : matrixKTransform ν α Q=Z) : S=Q := by
  let B : M := imaginaryPart S
  let C : M := imaginaryPart Q
  let RB := cfc (fun x => (Real.sqrt x)⁻¹) B
  let RC := cfc (fun x => (Real.sqrt x)⁻¹) C
  let Y := RB*(S-Q)*RC
  let U (T : selfAdjoint M) := matrixKResolvent S T.val
  let V (T : selfAdjoint M) := matrixKResolvent Q T.val
  let A (T : selfAdjoint M) := upperRowKernel α S B (U T)
  let D (T : selfAdjoint M) := upperRowKernel α Qᴴ C (V T)ᴴ
  let f (T : selfAdjoint M) := U T*(S-Q)*V T
  have hSu := Matrix.isUnit_of_posDef_imaginaryPart hS
  have hQu := Matrix.isUnit_of_posDef_imaginaryPart hQ
  have hQstar : IsUnit Qᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hQu.star
  have hcU : Continuous U := continuous_kResolvent_upper S hS
  have hcV : Continuous V := continuous_kResolvent_upper Q hQ
  have hcA : Continuous A := by dsimp only [A,upperRowKernel]; fun_prop
  have hcD : Continuous D := by dsimp only [D,upperRowKernel]; fun_prop
  have hiAA : Integrable (fun T => A T*(A T)ᴴ) ν :=
    integrable_continuous_compact_support ν hν (hcA.mul hcA.star)
  have hiDD : Integrable (fun T => D T*(D T)ᴴ) ν :=
    integrable_continuous_compact_support ν hν (hcD.mul hcD.star)
  have hiAD : Integrable (fun T => A T*Y*(D T)ᴴ) ν :=
    integrable_continuous_compact_support ν hν ((hcA.mul continuous_const).mul hcD.star)
  have hif : Integrable f ν :=
    integrable_continuous_compact_support ν hν ((hcU.mul continuous_const).mul hcV)
  have hIdS := imaginaryPart_matrixKTransform ν hν α S hS
  rw [hKS] at hIdS
  have hIdQ := imaginaryPart_matrixKTransform_dual ν hν α Q hQ
  rw [hKQ] at hIdQ
  have hdefS : (1-∫ T,A T*(A T)ᴴ ∂ν).PosDef :=
    upperRowKernel_defect ν hν α hα S B (imaginaryPart Z) hSu hS hZ U hcU hIdS
  have hdual : (imaginaryPart Z : M) =
      α⁻¹ • ((Qᴴ)⁻¹*C*((Qᴴ)⁻¹)ᴴ)-∫ T,(V T)ᴴ*C*((V T)ᴴ)ᴴ ∂ν := by
    simpa only [Matrix.conjTranspose_nonsing_inv,Matrix.conjTranspose_conjTranspose] using hIdQ
  have hdefQ : (1-∫ T,D T*(D T)ᴴ ∂ν).PosDef :=
    upperRowKernel_defect ν hν α hα Qᴴ C (imaginaryPart Z) hQstar hQ hZ
      (fun T => (V T)ᴴ) hcV.star hdual
  have hdiff := matrixKTransform_sub_matrixKTransform ν hν α
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hS)
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hQ)
  rw [hKS,hKQ,sub_self] at hdiff
  have heq : α⁻¹ • (S⁻¹*(S-Q)*Q⁻¹)=∫ T,f T ∂ν := sub_eq_zero.mp hdiff.symm
  have hcross : (∫ T,A T*Y*(D T)ᴴ ∂ν) =
      α • ((RB*S)*(∫ T,f T ∂ν)*(Q*RC)) := by
    calc
      _ = ∫ T,α • ((RB*S)*f T*(Q*RC)) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun T => upperRowKernel_mixed α hα.le S Q B C (U T) (V T) (S-Q) hS hQ
      _ = _ := by
        rw [integral_smul]
        congr 1
        exact (ContinuousLinearMap.mulLeftRight ℝ M (RB*S) (Q*RC)).integral_comp_comm hif
  have hfix : Y=∫ T,A T*Y*(D T)ᴴ ∂ν := by
    rw [hcross,← heq,Matrix.mul_smul,Matrix.smul_mul,smul_smul,
      mul_inv_cancel₀ hα.ne',one_smul]
    change RB*(S-Q)*RC=(RB*S)*(S⁻¹*(S-Q)*Q⁻¹)*(Q*RC)
    calc
      _ = RB*(S*S⁻¹)*(S-Q)*(Q⁻¹*Q)*RC := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hSu),
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hQu)]
        simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hzero := eq_zero_of_integral_cross_kernel_fixedPoint A D Y hiAA hiDD hiAD hdefS hdefQ hfix
  have hh := congrArg (fun X => cfc Real.sqrt B*X*cfc Real.sqrt C) hzero
  change cfc Real.sqrt B*(RB*(S-Q)*RC)*cfc Real.sqrt C=
    cfc Real.sqrt B*0*cfc Real.sqrt C at hh
  have hcan : cfc Real.sqrt B*(RB*(S-Q)*RC)*cfc Real.sqrt C=S-Q := by
    change cfc Real.sqrt B*(cfc (fun x => (Real.sqrt x)⁻¹) B*(S-Q)*
      cfc (fun x => (Real.sqrt x)⁻¹) C)*cfc Real.sqrt C=S-Q
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,cfc_sqrt_mul_inv_sqrt hS,Matrix.one_mul,
      Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hQ,Matrix.mul_one]
  rw [hcan,Matrix.mul_zero,Matrix.zero_mul] at hh
  exact sub_eq_zero.mp hh

private theorem matrixKTransformDeriv_integral_upper
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (S Δ : M) (hS : (imaginaryPart S : M).PosDef) :
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (S⁻¹*Δ*S⁻¹) -
      ∫ T, matrixKResolvent S T.val*Δ*matrixKResolvent S T.val ∂ν := by
  have hU := continuous_kResolvent_upper S hS
  have hi : Integrable (fun T : selfAdjoint M => matrixKResolventDeriv S T.val) ν := by
    have hRC := ((ContinuousLinearMap.mulLeftRight ℝ M).continuous.comp hU).clm_apply hU
    have hh := hRC.neg.continuousOn.integrableOn_compact (μ := ν) hν
    have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
    rwa [IntegrableOn,hre] at hh
  unfold matrixKTransformDeriv
  rw [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.integral_apply hi Δ]
  simp only [matrixKResolventDeriv,_root_.neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    integral_neg]
  abel

/-- The actual complex K derivative is invertible at every genuine
upper-half-plane solution with an upper-half-plane image. Both strict
contraction defects are consequences of the native imaginary identities;
no linearized stability conclusion is assumed.
Source: Montanari--Saeed (2026), Appendix A, local branch step in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem injective_matrixKTransformDerivComplex_of_upperHalfPlane
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M)
    (hS : (imaginaryPart S : M).PosDef)
    (hK : (imaginaryPart (matrixKTransform ν α S) : M).PosDef) :
    Function.Injective (matrixKTransformDerivComplex ν α S) := by
  have hzero (Δ : M) (hΔ : matrixKTransformDerivComplex ν α S Δ=0) : Δ=0 := by
    let B : M := imaginaryPart S
    let R := cfc (fun x => (Real.sqrt x)⁻¹) B
    let Y := R*Δ*R
    let U (T : selfAdjoint M) := matrixKResolvent S T.val
    let A (T : selfAdjoint M) := upperRowKernel α S B (U T)
    let D (T : selfAdjoint M) := upperRowKernel α Sᴴ B (U T)ᴴ
    let f (T : selfAdjoint M) := U T*Δ*U T
    have hSu := Matrix.isUnit_of_posDef_imaginaryPart hS
    have hSstar : IsUnit Sᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hSu.star
    have hcU : Continuous U := continuous_kResolvent_upper S hS
    have hcA : Continuous A := by dsimp only [A,upperRowKernel]; fun_prop
    have hcD : Continuous D := by dsimp only [D,upperRowKernel]; fun_prop
    have hiAA : Integrable (fun T => A T*(A T)ᴴ) ν :=
      integrable_continuous_compact_support ν hν (hcA.mul hcA.star)
    have hiDD : Integrable (fun T => D T*(D T)ᴴ) ν :=
      integrable_continuous_compact_support ν hν (hcD.mul hcD.star)
    have hiAD : Integrable (fun T => A T*Y*(D T)ᴴ) ν :=
      integrable_continuous_compact_support ν hν ((hcA.mul continuous_const).mul hcD.star)
    have hif : Integrable f ν :=
      integrable_continuous_compact_support ν hν ((hcU.mul continuous_const).mul hcU)
    have hIdS := imaginaryPart_matrixKTransform ν hν α S hS
    have hIdD := imaginaryPart_matrixKTransform_dual ν hν α S hS
    have hdefA : (1-∫ T,A T*(A T)ᴴ ∂ν).PosDef :=
      upperRowKernel_defect ν hν α hα S B (imaginaryPart (matrixKTransform ν α S))
        hSu hS hK U hcU hIdS
    have hdual : (imaginaryPart (matrixKTransform ν α S) : M) =
        α⁻¹ • ((Sᴴ)⁻¹*B*((Sᴴ)⁻¹)ᴴ)-∫ T,(U T)ᴴ*B*((U T)ᴴ)ᴴ ∂ν := by
      simpa only [Matrix.conjTranspose_nonsing_inv,Matrix.conjTranspose_conjTranspose] using hIdD
    have hdefD : (1-∫ T,D T*(D T)ᴴ ∂ν).PosDef :=
      upperRowKernel_defect ν hν α hα Sᴴ B (imaginaryPart (matrixKTransform ν α S))
        hSstar hS hK (fun T => (U T)ᴴ) hcU.star hdual
    have hDreal : matrixKTransformDeriv ν α S Δ=0 := by
      have he := congrArg (fun L : M →L[ℝ] M => L Δ)
        (matrixKTransformDerivComplex_restrictScalars ν α S)
      exact he.symm.trans hΔ
    have heq : α⁻¹ • (S⁻¹*Δ*S⁻¹)=∫ T,f T ∂ν := by
      apply sub_eq_zero.mp
      exact (matrixKTransformDeriv_integral_upper ν hν α S Δ hS).symm.trans hDreal
    have hcross : (∫ T,A T*Y*(D T)ᴴ ∂ν) =
        α • ((R*S)*(∫ T,f T ∂ν)*(S*R)) := by
      calc
        _ = ∫ T,α • ((R*S)*f T*(S*R)) ∂ν := by
          apply integral_congr_ae
          exact ae_of_all _ fun T => upperRowKernel_mixed α hα.le S S B B (U T) (U T) Δ hS hS
        _ = _ := by
          rw [integral_smul]
          congr 1
          exact (ContinuousLinearMap.mulLeftRight ℝ M (R*S) (S*R)).integral_comp_comm hif
    have hfix : Y=∫ T,A T*Y*(D T)ᴴ ∂ν := by
      rw [hcross,← heq,Matrix.mul_smul,Matrix.smul_mul,smul_smul,
        mul_inv_cancel₀ hα.ne',one_smul]
      change R*Δ*R=(R*S)*(S⁻¹*Δ*S⁻¹)*(S*R)
      calc
        _ = R*(S*S⁻¹)*Δ*(S⁻¹*S)*R := by
          rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hSu),
            Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hSu)]
          simp
        _ = _ := by simp only [Matrix.mul_assoc]
    have hy := eq_zero_of_integral_cross_kernel_fixedPoint A D Y hiAA hiDD hiAD hdefA hdefD hfix
    have hh := congrArg (fun X => cfc Real.sqrt B*X*cfc Real.sqrt B) hy
    change cfc Real.sqrt B*(R*Δ*R)*cfc Real.sqrt B=
      cfc Real.sqrt B*0*cfc Real.sqrt B at hh
    have hcan : cfc Real.sqrt B*(R*Δ*R)*cfc Real.sqrt B=Δ := by
      change cfc Real.sqrt B*(cfc (fun x => (Real.sqrt x)⁻¹) B*Δ*
        cfc (fun x => (Real.sqrt x)⁻¹) B)*cfc Real.sqrt B=Δ
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,cfc_sqrt_mul_inv_sqrt hS,Matrix.one_mul,
        Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hS,Matrix.mul_one]
    rw [hcan,Matrix.mul_zero,Matrix.zero_mul] at hh
    exact hh
  intro X Y hXY
  exact sub_eq_zero.mp (hzero (X-Y) (by rw [map_sub,hXY,sub_self]))

/-- A genuine upper-half-plane solution has a native local analytic
inverse for scalar spectral parameters. The inverse theorem uses the
proved actual complex derivative, with injectivity supplied by the true
upper-half-plane identities. Global branch existence remains separate.
Source: Montanari--Saeed (2026), Appendix A, local branch step in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_inverse_branch_of_upperHalfPlane
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : (imaginaryPart S : M).PosDef)
    (hKpos : (imaginaryPart (matrixKTransform ν α S) : M).PosDef)
    (u : ℂ) (hK : matrixKTransform ν α S=u•1) :
    ∃ G : ℂ → M, AnalyticAt ℂ G u ∧ G u=S ∧
      ∀ᶠ z in 𝓝 u, G z ∈ matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z)=z•1 := by
  have hdomain := mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hS
  let D := matrixKTransformDerivComplex ν α S
  have hinj : Function.Injective D :=
    injective_matrixKTransformDerivComplex_of_upperHalfPlane ν hν α hα S hS hKpos
  let e : M ≃L[ℂ] M := (LinearEquiv.ofBijective D.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hderiv : HasFDerivAt (matrixKTransform ν α) (e : M →L[ℂ] M) S := by
    convert! hasFDerivAt_matrixKTransform_complex ν hν α hdomain using 1
  have hc := contDiffAt_matrixKTransform_complex ν hν α hdomain
  let Q := hc.localInverse hderiv one_ne_zero
  let G : ℂ → M := fun z => Q (z•1)
  have hQ := hc.to_localInverse hderiv one_ne_zero
  have hG : ContDiffAt ℂ 1 G u := by
    apply ContDiffAt.comp u (g := Q) (f := fun z : ℂ => z•(1 : M))
    · rwa [← hK]
    · exact contDiffAt_id.smul contDiffAt_const
  have hGa : AnalyticAt ℂ G u :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      ((hG.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have hG₀ : G u=S := by
    change Q (u•1)=S
    rw [← hK]
    exact hc.localInverse_apply_image hderiv one_ne_zero
  refine ⟨G,hGa,hG₀,?_⟩
  have hcont : Filter.Tendsto G (𝓝 u) (𝓝 S) := by
    simpa only [hG₀] using hGa.continuousAt.tendsto
  have heq := (hc.hasStrictFDerivAt' hderiv one_ne_zero).eventually_right_inverse
  have hZ : Filter.Tendsto (fun z : ℂ => z•(1 : M))
      (𝓝 u) (𝓝 (matrixKTransform ν α S)) := by
    rw [hK]
    exact (continuous_id.smul continuous_const).continuousAt
  filter_upwards [hcont.eventually ((isOpen_matrixKTransformDomain ν hν).mem_nhds hdomain),
    hZ.eventually heq] with z hz hsolve
  exact ⟨hz,hsolve⟩

end NLAlib

import NLAlib.Matrix.Functions.KTransformDifference
import NLAlib.Matrix.Functions.KTransformStability
import NLAlib.Matrix.Functions.PositiveCrossKernelIntegral

/-!
# Global injectivity of the actual stable K-transform

The two-point resolvent identity and the actual positive derivative
certificates give two strict row-Gram defects. The associated genuine
mixed integral has no nonzero fixed point. This proves global injectivity
without replacing the source transform by an abstract inverse interface.

Source: Montanari--Saeed (2026), Lemma 8; the argument here uses positive
two-by-two matrix blocks in place of the paper's tensor-power estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem integrable_of_continuousOn_support
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) {f : selfAdjoint (Matrix n n ℂ) → Matrix n n ℂ}
    (hf : ContinuousOn f ν.support) : Integrable f ν := by
  have hi := hf.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

private theorem continuousOn_resolvent_support
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val)
      ν.support := by
  intro T hT
  exact ((continuousAt_matrixKResolvent S T.val
    (isUnit_matrixKDenominator S T.val hS (hgap T hT))).comp
      (f := fun T : selfAdjoint (Matrix n n ℂ) => (S,T.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt).continuousWithinAt

private theorem matrixKTransformDeriv_resolvent_integral
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (S B : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    matrixKTransformDeriv ν α S B = α⁻¹ • (S⁻¹*B*S⁻¹) -
      ∫ T, matrixKResolvent S T.val * B * matrixKResolvent S T.val ∂ν := by
  have hi := (integrable_matrixK_kernels ν hν S hS hgap).1
  unfold matrixKTransformDeriv
  rw [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.integral_apply hi B]
  simp only [matrixKResolventDeriv,_root_.neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    integral_neg]
  abel

private def stabilityRowKernel (α : ℝ) (S B T : Matrix n n ℂ) : Matrix n n ℂ :=
  Real.sqrt α • (cfc (fun x => (Real.sqrt x)⁻¹) B * S *
    matrixKResolvent S T * cfc Real.sqrt B)

private theorem continuousOn_stabilityRowKernel
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ) (S B : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => stabilityRowKernel α S B T.val)
      ν.support := by
  unfold stabilityRowKernel
  exact ((continuous_const.continuousOn.mul
    (continuousOn_resolvent_support ν S hS hgap)).mul continuous_const.continuousOn).const_smul
      (Real.sqrt α)

private theorem stabilityRowKernel_gram
    (α : ℝ) (hα : 0 ≤ α) (S B T : Matrix n n ℂ)
    (hS : S.PosDef) (hB : B.PosDef) (hT : T.IsHermitian) (hgap : (S⁻¹+T).PosDef) :
    stabilityRowKernel α S B T * (stabilityRowKernel α S B T)ᴴ =
      α • ((cfc (fun x => (Real.sqrt x)⁻¹) B*S) *
        (matrixKResolvent S T*B*matrixKResolvent S T) *
        (cfc (fun x => (Real.sqrt x)⁻¹) B*S)ᴴ) := by
  have hRB : (cfc (fun x => (Real.sqrt x)⁻¹) B).IsHermitian := cfc_predicate _ _
  have hQB : (cfc Real.sqrt B).IsHermitian := cfc_predicate _ _
  have hR := isHermitian_matrixKResolvent S T hS hT hgap
  simp only [stabilityRowKernel,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_mul,hRB.eq,hQB.eq,hS.isHermitian.eq,hR.eq,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [show Real.sqrt α * Real.sqrt α = α by exact Real.mul_self_sqrt hα]
  congr 1
  have hBB := cfc_sqrt_mul_self hB
  simpa only [Matrix.mul_assoc] using congrArg
    (fun X => cfc (fun x => (Real.sqrt x)⁻¹) B*S*matrixKResolvent S T*X*
      matrixKResolvent S T*S*cfc (fun x => (Real.sqrt x)⁻¹) B) hBB

private theorem stabilityRowKernel_defect
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α) (S B : Matrix n n ℂ)
    (hS : S.PosDef) (hB : B.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hD : (matrixKTransformDeriv ν α S B).PosDef) :
    (1-∫ T, stabilityRowKernel α S B T.val *
      (stabilityRowKernel α S B T.val)ᴴ ∂ν).PosDef := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) B
  let P := R*S
  let f := fun T : selfAdjoint (Matrix n n ℂ) =>
    matrixKResolvent S T.val * B * matrixKResolvent S T.val
  have hR : R.IsHermitian := cfc_predicate _ _
  have hi : Integrable f ν := integrable_of_continuousOn_support ν hν
    (((continuousOn_resolvent_support ν S hS hgap).mul continuous_const.continuousOn).mul
      (continuousOn_resolvent_support ν S hS hgap))
  have he : (∫ T, stabilityRowKernel α S B T.val *
      (stabilityRowKernel α S B T.val)ᴴ ∂ν) = α • (P*(∫ T, f T ∂ν)*Pᴴ) := by
    calc
      _ = ∫ T, α • (P*f T*Pᴴ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ν.support_mem_ae] with T hT
        exact stabilityRowKernel_gram α hα.le S B T.val hS hB T.property (hgap T hT)
      _ = _ := by
        rw [integral_smul]
        congr 1
        let L := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) P Pᴴ
        exact L.integral_comp_comm hi
  have hbase : α • (P*(α⁻¹ • (S⁻¹*B*S⁻¹))*Pᴴ) = 1 := by
    have hb : R*B*R = 1 := by
      rw [← cfc_sqrt_mul_self hB]
      change R*(cfc Real.sqrt B*cfc Real.sqrt B)*R=1
      rw [← Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hB,Matrix.one_mul,
        cfc_sqrt_mul_inv_sqrt hB]
    simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hα.ne',one_smul,
      P,Matrix.conjTranspose_mul,hR.eq,hS.isHermitian.eq]
    calc
      _ = R*(S*S⁻¹)*B*(S⁻¹*S)*R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit),
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
        simpa only [Matrix.mul_one,Matrix.one_mul] using hb
  have heq : (1-∫ T, stabilityRowKernel α S B T.val *
      (stabilityRowKernel α S B T.val)ᴴ ∂ν) =
      α • (P*matrixKTransformDeriv ν α S B*Pᴴ) := by
    rw [he,matrixKTransformDeriv_resolvent_integral ν hν α S B hS hgap,
      Matrix.mul_sub,Matrix.sub_mul,smul_sub,hbase]
  rw [heq]
  apply (posDef_real_smul_iff α hα _).mpr
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    ((isUnit_cfc_invSqrt B hB).mul hS.isUnit)).mpr hD

private theorem stabilityRowKernel_mixed
    (α : ℝ) (hα : 0 ≤ α) (S Q B C T : Matrix n n ℂ)
    (hQ : Q.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hT : T.IsHermitian) (hgap : (Q⁻¹+T).PosDef) (Δ : Matrix n n ℂ) :
    stabilityRowKernel α S B T *
        (cfc (fun x => (Real.sqrt x)⁻¹) B*Δ*cfc (fun x => (Real.sqrt x)⁻¹) C) *
          (stabilityRowKernel α Q C T)ᴴ =
      α • ((cfc (fun x => (Real.sqrt x)⁻¹) B*S) *
        (matrixKResolvent S T*Δ*matrixKResolvent Q T) *
        (Q*cfc (fun x => (Real.sqrt x)⁻¹) C)) := by
  have hRC : (cfc (fun x => (Real.sqrt x)⁻¹) C).IsHermitian := cfc_predicate _ _
  have hQC : (cfc Real.sqrt C).IsHermitian := cfc_predicate _ _
  have hR := isHermitian_matrixKResolvent Q T hQ hT hgap
  simp only [stabilityRowKernel,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_mul,hRC.eq,hQC.eq,hQ.isHermitian.eq,hR.eq,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [show Real.sqrt α * Real.sqrt α = α by exact Real.mul_self_sqrt hα]
  congr 1
  calc
    _ = cfc (fun x => (Real.sqrt x)⁻¹) B*S*matrixKResolvent S T*
        (cfc Real.sqrt B*cfc (fun x => (Real.sqrt x)⁻¹) B)*Δ*
        (cfc (fun x => (Real.sqrt x)⁻¹) C*cfc Real.sqrt C)*
        matrixKResolvent Q T*Q*cfc (fun x => (Real.sqrt x)⁻¹) C := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [cfc_sqrt_mul_inv_sqrt hB,cfc_inv_sqrt_mul_sqrt hC]
      simp only [Matrix.mul_one,Matrix.mul_assoc]

/-- The actual compactly supported K-transform is globally injective on
the positive admissible region with genuine positive derivative witnesses.
The witnesses imply strict mixed-kernel defects; no global inverse,
resolvent law, or mixed-map contraction is supplied as a hypothesis.
Source: Montanari--Saeed (2026), Lemma 8.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_eq_iff_eq_of_derivative_witness
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S Q : Matrix n n ℂ) (hS : S.PosDef) (hQ : Q.PosDef)
    (hgapS : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hgapQ : ∀ T ∈ ν.support, (Q⁻¹+T.val).PosDef)
    (hwS : ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef)
    (hwQ : ∃ C : Matrix n n ℂ, C.PosDef ∧ (matrixKTransformDeriv ν α Q C).PosDef) :
    matrixKTransform ν α S = matrixKTransform ν α Q ↔ S=Q := by
  constructor
  · intro hK
    obtain ⟨B,hB,hDB⟩ := hwS
    obtain ⟨C,hC,hDC⟩ := hwQ
    let RB := cfc (fun x => (Real.sqrt x)⁻¹) B
    let RC := cfc (fun x => (Real.sqrt x)⁻¹) C
    let Y := RB*(S-Q)*RC
    let A := fun T : selfAdjoint (Matrix n n ℂ) => stabilityRowKernel α S B T.val
    let D := fun T : selfAdjoint (Matrix n n ℂ) => stabilityRowKernel α Q C T.val
    let f := fun T : selfAdjoint (Matrix n n ℂ) =>
      matrixKResolvent S T.val*(S-Q)*matrixKResolvent Q T.val
    have hcA := continuousOn_stabilityRowKernel ν α S B hS hgapS
    have hcD := continuousOn_stabilityRowKernel ν α Q C hQ hgapQ
    have hiAA : Integrable (fun T => A T*(A T)ᴴ) ν :=
      integrable_of_continuousOn_support ν hν (hcA.mul hcA.star)
    have hiDD : Integrable (fun T => D T*(D T)ᴴ) ν :=
      integrable_of_continuousOn_support ν hν (hcD.mul hcD.star)
    have hiAD : Integrable (fun T => A T*Y*(D T)ᴴ) ν :=
      integrable_of_continuousOn_support ν hν
        ((hcA.mul continuous_const.continuousOn).mul hcD.star)
    have hif : Integrable f ν := integrable_of_continuousOn_support ν hν
      (((continuousOn_resolvent_support ν S hS hgapS).mul continuous_const.continuousOn).mul
        (continuousOn_resolvent_support ν Q hQ hgapQ))
    have hdiff := matrixKTransform_sub_matrixKTransform ν hν α
      ⟨hS.isUnit,fun T hT => isUnit_matrixKDenominator S T.val hS (hgapS T hT)⟩
      ⟨hQ.isUnit,fun T hT => isUnit_matrixKDenominator Q T.val hQ (hgapQ T hT)⟩
    rw [hK,sub_self] at hdiff
    have heq : α⁻¹ • (S⁻¹*(S-Q)*Q⁻¹) = ∫ T, f T ∂ν :=
      sub_eq_zero.mp hdiff.symm
    have hcross : (∫ T, A T*Y*(D T)ᴴ ∂ν) =
        α • ((RB*S)*(∫ T, f T ∂ν)*(Q*RC)) := by
      calc
        _ = ∫ T, α • ((RB*S)*f T*(Q*RC)) ∂ν := by
          apply integral_congr_ae
          filter_upwards [ν.support_mem_ae] with T hT
          exact stabilityRowKernel_mixed α hα.le S Q B C T.val hQ hB hC
            T.property (hgapQ T hT) (S-Q)
        _ = _ := by
          rw [integral_smul]
          congr 1
          let L := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RB*S) (Q*RC)
          exact L.integral_comp_comm hif
    have hfix : Y = ∫ T, A T*Y*(D T)ᴴ ∂ν := by
      rw [hcross,← heq,Matrix.mul_smul,Matrix.smul_mul,smul_smul,
        mul_inv_cancel₀ hα.ne',one_smul]
      change RB*(S-Q)*RC = (RB*S)*(S⁻¹*(S-Q)*Q⁻¹)*(Q*RC)
      calc
        _ = RB*(S*S⁻¹)*(S-Q)*(Q⁻¹*Q)*RC := by
          rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit),
            Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit)]
          simp
        _ = _ := by simp only [Matrix.mul_assoc]
    have hzero := eq_zero_of_integral_cross_kernel_fixedPoint A D Y hiAA hiDD hiAD
      (stabilityRowKernel_defect ν hν α hα S B hS hB hgapS hDB)
      (stabilityRowKernel_defect ν hν α hα Q C hQ hC hgapQ hDC) hfix
    have hh := congrArg (fun X => cfc Real.sqrt B*X*cfc Real.sqrt C) hzero
    change cfc Real.sqrt B*(RB*(S-Q)*RC)*cfc Real.sqrt C =
      cfc Real.sqrt B*0*cfc Real.sqrt C at hh
    have hcan : cfc Real.sqrt B*(RB*(S-Q)*RC)*cfc Real.sqrt C = S-Q := by
      change cfc Real.sqrt B*(cfc (fun x => (Real.sqrt x)⁻¹) B*(S-Q)*
        cfc (fun x => (Real.sqrt x)⁻¹) C)*cfc Real.sqrt C = S-Q
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,cfc_sqrt_mul_inv_sqrt hB,
        Matrix.one_mul,Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hC,Matrix.mul_one]
    rw [hcan,Matrix.mul_zero,Matrix.zero_mul] at hh
    exact sub_eq_zero.mp hh
  · rintro rfl
    rfl

/-- Strict Frobenius positivity of the actual K derivative at both
admissible points implies global uniqueness for the original K equation.
This proves the global-injectivity bridge independently of the remaining
Stieltjes-law and spectral-support identification.
Source: Montanari--Saeed (2026), Lemma 8.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_eq_iff_eq_of_quadratic_pos [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S Q : Matrix n n ℂ) (hS : S.PosDef) (hQ : Q.PosDef)
    (hgapS : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hgapQ : ∀ T ∈ ν.support, (Q⁻¹+T.val).PosDef)
    (hstS : ∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ))
    (hstQ : ∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α Q Δ)) :
    matrixKTransform ν α S = matrixKTransform ν α Q ↔ S=Q := by
  have hwS := (matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S hS hgapS).mp
    ((matrixKTransform_norm_iff_supersolution ν hν α hα S hS hgapS).mp
      ((matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS hgapS).mp hstS))
  have hwQ := (matrixKTransform_supersolution_iff_derivative_witness ν hν α hα Q hQ hgapQ).mp
    ((matrixKTransform_norm_iff_supersolution ν hν α hα Q hQ hgapQ).mp
      ((matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα Q hQ hgapQ).mp hstQ))
  exact matrixKTransform_eq_iff_eq_of_derivative_witness ν hν α hα S Q hS hQ
    hgapS hgapQ hwS hwQ

end NLAlib

import NLAlib.Matrix.Functions.KTransformStableDomain
import NLAlib.ForMathlib.Analysis.Matrix.InverseTangent

/-! # Native inverse-variable convexity of the nonlinear K transform

The exact inverse tangent remainder gives a true positive stability
certificate at an ordered solution with a strictly decreased target.
This is the endpoint estimate for real order continuation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem inverseConvexity_integrable_samples
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support) :
    Integrable (fun T : selfAdjoint M => T.val) ν := by
  have hi := continuous_subtype_val.continuousOn.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

private theorem inverseConvexity_integrable_sandwich
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (Y : M) (hgap : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    Integrable (fun T : selfAdjoint M => T.val*(Y+T.val)⁻¹*T.val) ν := by
  have hc : ContinuousOn (fun T : selfAdjoint M => T.val*(Y+T.val)⁻¹*T.val) ν.support := by
    intro T hT
    have hi : ContinuousAt (fun U : selfAdjoint M => (Y+U.val)⁻¹) T :=
      (hasFDerivAt_matrixInverse (Y+T.val) (hgap T hT).isUnit).continuousAt.comp
        (f := fun U : selfAdjoint M => Y+U.val)
        (continuous_const.add continuous_subtype_val).continuousAt
    exact ((continuous_subtype_val.continuousAt.mul hi).mul
      continuous_subtype_val.continuousAt).continuousWithinAt
  have hi := hc.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

/-- On the actual real positive-gap domain, inverse variables turn the
native K resolvent into a constant minus a true resolvent sandwich.
Singular and indefinite samples are included. -/
theorem matrixKResolvent_inverse_eq (Y T : M) (hY : Y.PosDef)
    (hgap : (Y+T).PosDef) :
    matrixKResolvent Y⁻¹ T=T-T*(Y+T)⁻¹*T := by
  have hi : Y⁻¹⁻¹=Y := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)
  have hden : 1+Y⁻¹*T=Y⁻¹*(Y+T) := by
    rw [Matrix.mul_add,Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)]
  rw [matrixKResolvent,hden,Matrix.mul_inv_rev,hi]
  calc
    _ = T*(Y+T)⁻¹*Y := by rw [Matrix.mul_assoc]
    _ = T*(Y+T)⁻¹*((Y+T)-T) := congrArg (fun W : M => T*(Y+T)⁻¹*W) (by abel)
    _ = _ := by
      rw [Matrix.mul_sub,Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hgap.isUnit),Matrix.mul_one]

/-- The real inverse-variable expression is exactly the original K
transform, including every native sample integral and its normalization.
Source: algebraic inverse-variable form of Montanari--Saeed (2026), (8).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_inverse_eq
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (Y : M) (hY : Y.PosDef)
    (hgap : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    matrixKTransform ν α Y⁻¹=(∫ T : selfAdjoint M,T.val ∂ν)-
      (∫ T : selfAdjoint M,T.val*(Y+T.val)⁻¹*T.val ∂ν)-α⁻¹•Y := by
  have hiT := inverseConvexity_integrable_samples ν hν
  have hiR := inverseConvexity_integrable_sandwich ν hν Y hgap
  have hI : (∫ T : selfAdjoint M,matrixKResolvent Y⁻¹ T.val ∂ν)=
      (∫ T : selfAdjoint M,T.val ∂ν)-
      (∫ T : selfAdjoint M,T.val*(Y+T.val)⁻¹*T.val ∂ν) := by
    rw [← integral_sub hiT hiR]
    apply integral_congr_ae
    filter_upwards [ν.support_mem_ae] with T hT
    exact matrixKResolvent_inverse_eq Y T.val hY (hgap T hT)
  rw [matrixKTransform,hI,Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)]

/-- The native inverse stability defect dominates the exact decrease of
the K transform. This is the operator-convex tangent inequality, proved
from the actual positive inverse remainders under the sample integral.
No convexity or stability conclusion is supplied as a premise.
Source: Montanari--Saeed (2026), stable-domain continuation; inverse tangent argument.
atlas: block-wishart-variational-edges (partial) -/
theorem smul_matrixKTransform_inverse_sub_le_inverseStability_defect
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y Z : M) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y+T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z+T.val).PosDef) :
    α•(matrixKTransform ν α Y⁻¹-matrixKTransform ν α Z⁻¹)≤
      Z-Y-matrixKInverseStability ν α Z (Z-Y) := by
  have hiY := inverseConvexity_integrable_sandwich ν hν Y hgapY
  have hiZ := inverseConvexity_integrable_sandwich ν hν Z hgapZ
  have hiD := integrable_matrixKInverseStability_kernel ν hν Z (Z-Y) hgapZ
  have hI : (∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*(Z-Y)*(Z+T.val)⁻¹*T.val ∂ν)≤
      (∫ T : selfAdjoint M,T.val*(Y+T.val)⁻¹*T.val ∂ν)-
      (∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*T.val ∂ν) := by
    rw [← integral_sub hiY hiZ]
    apply integral_mono_ae hiD (hiY.sub hiZ)
    filter_upwards [ν.support_mem_ae] with T hT
    have ht := (hgapY T hT).inv_tangent_le (hgapZ T hT)
    have hP := (Matrix.le_iff.mp ht).mul_mul_conjTranspose_same T.val
    have hTH : T.val.IsHermitian := T.property
    apply Matrix.le_iff.mpr
    convert! hP using 1;
      simp only [Pi.sub_apply,show (Z+T.val)-(Y+T.val)=Z-Y by abel,
        Matrix.mul_sub,Matrix.sub_mul,hTH.eq,Matrix.mul_assoc]
  have hmono := smul_le_smul_of_nonneg_left hI hα.le
  rw [matrixKTransform_inverse_eq ν hν α Y hY hgapY,
    matrixKTransform_inverse_eq ν hν α Z hZ hgapZ,matrixKInverseStability]
  simp only [smul_sub,smul_smul,mul_inv_cancel₀ hα.ne',one_smul]
  convert! sub_le_sub_left hmono (Z-Y) using 1; module

/-- An ordered real inverse solution with a strictly decreased native K
target has a positive stability certificate. This includes a limit of
solutions: stability is proved from the actual secant difference, not
retained as a closedness assumption.
Source: Montanari--Saeed (2026), real stable-domain continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem posDef_sub_and_mem_matrixKInverseStableDomain_of_ordered_transform_decrease
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y Z : selfAdjoint M) (hY : Y.val.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y.val+T.val).PosDef) (hYZ : Y.val≤Z.val)
    (hK : (matrixKTransform ν α Y.val⁻¹-matrixKTransform ν α Z.val⁻¹).PosDef) :
    (Z.val-Y.val).PosDef ∧ Z∈matrixKInverseStableDomain ν α := by
  have hZ : Z.val.PosDef := (hY.isStrictlyPositive.of_le hYZ).posDef
  have hgapZ : ∀ T ∈ ν.support, (Z.val+T.val).PosDef := by
    intro T hT
    have hle : Y.val+T.val≤Z.val+T.val := by
      simpa only [add_comm] using add_le_add_right hYZ T.val
    exact ((hgapY T hT).isStrictlyPositive.of_le hle).posDef
  have hiY := inverseConvexity_integrable_sandwich ν hν Y.val hgapY
  have hiZ := inverseConvexity_integrable_sandwich ν hν Z.val hgapZ
  have hI : (∫ T : selfAdjoint M,T.val*(Z.val+T.val)⁻¹*T.val ∂ν)≤
      (∫ T : selfAdjoint M,T.val*(Y.val+T.val)⁻¹*T.val ∂ν) := by
    apply integral_mono_ae hiZ hiY
    filter_upwards [ν.support_mem_ae] with T hT
    have hinv : (Z.val+T.val)⁻¹≤(Y.val+T.val)⁻¹ := by
      have hle : Y.val+T.val≤Z.val+T.val := by
        simpa only [add_comm] using add_le_add_right hYZ T.val
      simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
        CStarAlgebra.ringInverse_le_ringInverse hle
          (hgapY T hT).isStrictlyPositive
    have hP := (Matrix.le_iff.mp hinv).mul_mul_conjTranspose_same T.val
    have hTH : T.val.IsHermitian := T.property
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub,Matrix.sub_mul,hTH.eq] using hP
  have hsec : α•(matrixKTransform ν α Y.val⁻¹-matrixKTransform ν α Z.val⁻¹)≤Z.val-Y.val := by
    rw [matrixKTransform_inverse_eq ν hν α Y.val hY hgapY,
      matrixKTransform_inverse_eq ν hν α Z.val hZ hgapZ]
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ hα.ne',one_smul]
    have hp := smul_le_smul_of_nonneg_left hI hα.le
    convert! add_le_add_left hp (Z.val-Y.val-
      α•(∫ T : selfAdjoint M,T.val*(Y.val+T.val)⁻¹*T.val ∂ν)) using 1 <;> module
  have hC : (Z.val-Y.val).PosDef := ((hK.smul hα).isStrictlyPositive.of_le hsec).posDef
  have hdef : (Z.val-Y.val-matrixKInverseStability ν α Z.val (Z.val-Y.val)).PosDef :=
    ((hK.smul hα).isStrictlyPositive.of_le
      (smul_matrixKTransform_inverse_sub_le_inverseStability_defect ν hν α hα
        Y.val Z.val hY hZ hgapY hgapZ)).posDef
  exact ⟨hC,hZ,hgapZ,Z.val-Y.val,hC,hdef⟩

end NLAlib

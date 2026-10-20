import NLAlib.Matrix.Functions.KTransformInverseConvexity

/-! # Properness bounds for ordered native real K solutions

An actual lower inverse-variable bound preserves every sample gap.
The true equation then bounds inverse variables uniformly over bounded
target sets, which supplies compactness for order continuation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- Actual ordered real K solutions have a norm bound from the sample
support and the genuine base resolvents. The positive gaps and all
inverse estimates follow from native Loewner order.
Source: Montanari--Saeed (2026), real order-continuation compactness.
atlas: block-wishart-variational-edges (partial) -/
theorem norm_ordered_matrixKTransform_inverse_solution_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y Z U : M) (hY : Y.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y+T.val).PosDef) (hYZ : Y≤Z)
    (hK : matrixKTransform ν α Z⁻¹=U) (R q : ℝ) (hR : 0≤R) (hq : 0≤q)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hbase : ∀ T ∈ ν.support, ‖(Y+T.val)⁻¹‖≤q) :
    ‖Z‖≤α*(‖U‖+R+R^2*q) := by
  have hZ : Z.PosDef := (hY.isStrictlyPositive.of_le hYZ).posDef
  have hgapZ : ∀ T ∈ ν.support, (Z+T.val).PosDef := by
    intro T hT
    have hle : Y+T.val≤Z+T.val := by simpa only [add_comm] using add_le_add_right hYZ T.val
    exact ((hgapY T hT).isStrictlyPositive.of_le hle).posDef
  have hET : ‖∫ T : selfAdjoint M,T.val ∂ν‖≤R := by
    have hpt : ∀ᵐ T : selfAdjoint M ∂ν, ‖T.val‖≤R := by
      filter_upwards [ν.support_mem_ae] with T hT
      simpa only [specNorm_eq_norm] using hbound T hT
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := ν) hpt
  have hER : ‖∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*T.val ∂ν‖≤R^2*q := by
    have hpt : ∀ᵐ T : selfAdjoint M ∂ν, ‖T.val*(Z+T.val)⁻¹*T.val‖≤R^2*q := by
      filter_upwards [ν.support_mem_ae] with T hT
      have hle : Y+T.val≤Z+T.val := by simpa only [add_comm] using add_le_add_right hYZ T.val
      have hinv : (Z+T.val)⁻¹≤(Y+T.val)⁻¹ := by
        simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
          CStarAlgebra.ringInverse_le_ringInverse hle (hgapY T hT).isStrictlyPositive
      have hRN : ‖(Z+T.val)⁻¹‖≤q :=
        (CStarAlgebra.norm_le_norm_of_nonneg_of_le
          (hgapZ T hT).inv.posSemidef.nonneg hinv).trans (hbase T hT)
      have hTN : ‖T.val‖≤R := by simpa only [specNorm_eq_norm] using hbound T hT
      calc
        _ ≤ ‖T.val‖*‖(Z+T.val)⁻¹‖*‖T.val‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ R*q*R := by gcongr
        _ = _ := by ring
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := ν) hpt
  have hz := congrArg (fun W : M => α•W) hK
  rw [matrixKTransform_inverse_eq ν hν α Z hZ hgapZ] at hz
  simp only [smul_sub,smul_smul,mul_inv_cancel₀ hα.ne',one_smul] at hz
  have hEq : Z=α•((∫ T : selfAdjoint M,T.val ∂ν)-
      (∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*T.val ∂ν)-U) := by
    rw [smul_sub,smul_sub]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hz).symm
  rw [hEq,norm_smul,Real.norm_of_nonneg hα.le]
  apply mul_le_mul_of_nonneg_left _ hα.le
  calc
    _ ≤ ‖(∫ T : selfAdjoint M,T.val ∂ν)-
        (∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*T.val ∂ν)‖+‖U‖ := norm_sub_le _ _
    _ ≤ ‖∫ T : selfAdjoint M,T.val ∂ν‖+
        ‖∫ T : selfAdjoint M,T.val*(Z+T.val)⁻¹*T.val ∂ν‖+‖U‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ R+R^2*q+‖U‖ := by gcongr
    _ = _ := by ring

/-- Compact native sample support makes the real inverse K map proper
on every actual lower order cone: bounded targets give bounded inverse
variables. The constant is constructed from the genuine sample
resolvents; no compactness conclusion is assumed.
Source: Montanari--Saeed (2026), real stable-domain continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_norm_bound_ordered_matrixKTransform_inverse
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y : M) (hY : Y.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    ∃ C : ℝ, 0≤C ∧ ∀ Z : M, Y≤Z →
      ‖Z‖≤α*(‖matrixKTransform ν α Z⁻¹‖+C) := by
  obtain ⟨R0,hR0⟩ := hν.isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0≤R := zero_le_one.trans (le_max_right _ _)
  have hbound : ∀ T ∈ ν.support, specNorm T.val≤R := by
    intro T hT
    have hb : specNorm T.val≤R0 := by
      simpa only [specNorm_eq_norm,← AddSubgroup.norm_coe] using hR0 T hT
    exact hb.trans (le_max_left _ _)
  have hc : ContinuousOn (fun T : selfAdjoint M => (Y+T.val)⁻¹) ν.support := by
    intro T hT
    exact ((hasFDerivAt_matrixInverse (Y+T.val) (hgapY T hT).isUnit).continuousAt.comp
      (f := fun T : selfAdjoint M => Y+T.val)
      (continuous_const.add continuous_subtype_val).continuousAt).continuousWithinAt
  obtain ⟨q0,hq0⟩ := (hν.image_of_continuousOn hc).isBounded.exists_norm_le
  let q := max q0 1
  have hq : 0≤q := zero_le_one.trans (le_max_right _ _)
  have hbase : ∀ T ∈ ν.support, ‖(Y+T.val)⁻¹‖≤q := by
    intro T hT
    exact (hq0 _ ⟨T,hT,rfl⟩).trans (le_max_left _ _)
  refine ⟨R+R^2*q,by positivity,?_⟩
  intro Z hZ
  simpa only [add_assoc] using norm_ordered_matrixKTransform_inverse_solution_le ν hν α hα
    Y Z (matrixKTransform ν α Z⁻¹) hY hgapY hZ rfl R q hR hq hbound hbase

end NLAlib

import NLAlib.Matrix.Functions.KTransformInverseConcavity
import NLAlib.Matrix.Functions.KTransformComplexCalculus
import NLAlib.ForMathlib.Topology.Order.CompactMonotoneFixedPoint
import NLAlib.ForMathlib.Analysis.CStarAlgebra.CompactOrderInterval

/-! # Genuine stable K solutions from strict inverse subsolutions

The actual order-preserving resolvent iteration has a compact invariant
order interval. Compact monotone iteration constructs its fixed point.
The true secant defect then proves strict stability at that fixed point.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual positive inverse-variable resolvent iteration at target U. -/
def matrixKInverseIteration (ν : Measure (selfAdjoint M)) (α : ℝ) (U Y : M) : M :=
  α • ((∫ T : selfAdjoint M, T.val ∂ν) -
    (∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν) - U)

/-- The literal iteration residual is exactly the original K equation. -/
theorem matrixKInverseIteration_eq_add_transform
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : α ≠ 0) (U Y : M) (hY : Y.PosDef)
    (hgap : ∀ T ∈ ν.support, (Y + T.val).PosDef) :
    matrixKInverseIteration ν α U Y = Y + α • (matrixKTransform ν α Y⁻¹ - U) := by
  rw [matrixKTransform_inverse_eq ν hν α Y hY hgap]
  simp only [matrixKInverseIteration, smul_sub, smul_smul, mul_inv_cancel₀ hα, one_smul]
  module

private theorem inverseIteration_gap_of_le
    (ν : Measure (selfAdjoint M)) (Y Z : M)
    (hY : Y.PosDef) (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef) (hYZ : Y ≤ Z) :
    Z.PosDef ∧ ∀ T ∈ ν.support, (Z + T.val).PosDef := by
  refine ⟨(hY.isStrictlyPositive.of_le hYZ).posDef, ?_⟩
  intro T hT
  have hle : Y + T.val ≤ Z + T.val := by
    simpa only [add_comm] using add_le_add_right hYZ T.val
  exact ((hgapY T hT).isStrictlyPositive.of_le hle).posDef

/-- The genuine inverse-variable iteration is order-preserving on every
actual positive sample-gap cone. No monotonicity premise is supplied. -/
theorem matrixKInverseIteration_le_of_le
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 ≤ α) (U Y Z : M)
    (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef) (hYZ : Y ≤ Z) :
    matrixKInverseIteration ν α U Y ≤ matrixKInverseIteration ν α U Z := by
  have hiY := integrable_matrixKInverseSandwich ν hν Y hgapY
  have hiZ := integrable_matrixKInverseSandwich ν hν Z hgapZ
  have hI : (∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν) ≤
      ∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν := by
    apply integral_mono_ae hiZ hiY
    filter_upwards [ν.support_mem_ae] with T hT
    have hle : Y + T.val ≤ Z + T.val := by
      simpa only [add_comm] using add_le_add_right hYZ T.val
    have hinv : (Z + T.val)⁻¹ ≤ (Y + T.val)⁻¹ := by
      simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
        CStarAlgebra.ringInverse_le_ringInverse hle
          (hgapY T hT).isStrictlyPositive
    have hTH : T.val.IsHermitian := T.property
    have hp := (Matrix.le_iff.mp hinv).mul_mul_conjTranspose_same T.val
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, hTH.eq] using hp
  exact smul_le_smul_of_nonneg_left
    (sub_le_sub_right (sub_le_sub_left hI (∫ T : selfAdjoint M, T.val ∂ν)) U) hα

/-- Every true iterate has the same explicit upper bound, obtained from
positivity of its actual resolvent sandwich. -/
theorem matrixKInverseIteration_le_upper
    (ν : Measure (selfAdjoint M)) (α : ℝ) (hα : 0 ≤ α) (U Y : M)
    (hgap : ∀ T ∈ ν.support, (Y + T.val).PosDef) :
    matrixKInverseIteration ν α U Y ≤ α • ((∫ T : selfAdjoint M, T.val ∂ν) - U) := by
  have hI : 0 ≤ ∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ν.support_mem_ae] with T hT
    have hTH : T.val.IsHermitian := T.property
    have hp := (hgap T hT).inv.posSemidef.mul_mul_conjTranspose_same T.val
    exact Matrix.nonneg_iff_posSemidef.mpr (by simpa only [hTH.eq] using hp)
  exact smul_le_smul_of_nonneg_left
    (sub_le_sub_right (sub_le_self _ hI) U) hα

/-- Every actual strict inverse-variable subsolution constructs an ordered
solution in the original stable region. The initial point need only have
positive actual sample gaps; its stability is not assumed. The true fixed
point and its stability are proved by compact monotone iteration and the
native inverse tangent defect.
Source: inverse-variable concavity route for Montanari--Saeed (2026).
atlas: block-wishart-log-potential (partial) -/
theorem exists_stable_matrixKTransform_inverse_solution_of_strict_subsolution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (Y : selfAdjoint M) (hY : Y.val.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y.val + T.val).PosDef)
    (U : M) (hdec : (matrixKTransform ν α Y.val⁻¹ - U).PosDef) :
    ∃ Z : selfAdjoint M, (Z.val - Y.val).PosDef ∧
      Z ∈ matrixKInverseStableDomain ν α ∧ matrixKTransform ν α Z.val⁻¹ = U := by
  let F := matrixKInverseIteration ν α U
  let B := α • ((∫ T : selfAdjoint M, T.val ∂ν) - U)
  let K := Icc Y.val B
  have hsub : Y.val ≤ F Y.val := by
    have he := matrixKInverseIteration_eq_add_transform ν hν α hα.ne' U Y.val hY hgapY
    have hp : (F Y.val - Y.val).PosDef := by
      rw [show F Y.val = Y.val + α • (matrixKTransform ν α Y.val⁻¹ - U) from he]
      simpa only [add_sub_cancel_left] using hdec.smul hα
    exact Matrix.le_iff.mpr hp.posSemidef
  have hYB : Y.val ≤ B := hsub.trans (matrixKInverseIteration_le_upper ν α hα.le U Y.val hgapY)
  have hmap : MapsTo F K K := by
    intro Z hZ
    obtain ⟨hZpos, hgapZ⟩ := inverseIteration_gap_of_le ν Y.val Z hY hgapY hZ.1
    exact ⟨hsub.trans (matrixKInverseIteration_le_of_le ν hν α hα.le U Y.val Z hgapY hgapZ hZ.1),
      matrixKInverseIteration_le_upper ν α hα.le U Z hgapZ⟩
  have hmono : MonotoneOn F K := by
    intro Z hZ W hW hZW
    exact matrixKInverseIteration_le_of_le ν hν α hα.le U Z W
      (inverseIteration_gap_of_le ν Y.val Z hY hgapY hZ.1).2
      (inverseIteration_gap_of_le ν Y.val W hY hgapY hW.1).2 hZW
  have hcont : ContinuousOn F K := by
    have hc : ContinuousOn
        (fun Z : M => Z + α • (matrixKTransform ν α Z⁻¹ - U)) K := by
      intro Z hZ
      obtain ⟨hZpos, hgapZ⟩ := inverseIteration_gap_of_le ν Y.val Z hY hgapY hZ.1
      have hZZ : Z⁻¹⁻¹ = Z := Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hZpos.isUnit)
      have hdom : Z⁻¹ ∈ matrixKTransformDomain ν :=
        ⟨hZpos.inv.isUnit, fun T hT => isUnit_matrixKDenominator Z⁻¹ T.val hZpos.inv
          (by simpa only [hZZ] using hgapZ T hT)⟩
      have hi := (hasFDerivAt_matrixInverse Z hZpos.isUnit).continuousAt
      have hk := (hasFDerivAt_matrixKTransform_complex ν hν α hdom).continuousAt.comp hi
      change ContinuousAt (fun V : M => matrixKTransform ν α V⁻¹) Z at hk
      have hcA : ContinuousAt (fun V : M => V + α • (matrixKTransform ν α V⁻¹ - U)) Z :=
        continuousAt_id.add ((continuousAt_const (y := α)).smul
          (hk.sub (continuousAt_const (y := U))))
      exact hcA.continuousWithinAt
    apply hc.congr
    intro Z hZ
    obtain ⟨hZpos, hgapZ⟩ := inverseIteration_gap_of_le ν Y.val Z hY hgapY hZ.1
    exact matrixKInverseIteration_eq_add_transform ν hν α hα.ne' U Z hZpos hgapZ
  obtain ⟨Z, hZ, hfix, _hiterates⟩ := (CStarAlgebra.isCompact_Icc Y.val B).exists_fixedPoint_of_monotoneOn
    hcont hmap hmono (show Y.val ∈ K from ⟨le_rfl, hYB⟩) hsub
  obtain ⟨hZpos, hgapZ⟩ := inverseIteration_gap_of_le ν Y.val Z hY hgapY hZ.1
  have he := matrixKInverseIteration_eq_add_transform ν hν α hα.ne' U Z hZpos hgapZ
  have hzero : α • (matrixKTransform ν α Z⁻¹ - U) = 0 := by
    change matrixKInverseIteration ν α U Z = Z at hfix
    rw [he] at hfix
    exact add_left_cancel (a := Z) (by simpa only [add_zero] using hfix)
  have hKZ : matrixKTransform ν α Z⁻¹ = U :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hα.ne')
  let Zsa : selfAdjoint M := ⟨Z, hZpos.isHermitian⟩
  have hsec : (matrixKTransform ν α Y.val⁻¹ - matrixKTransform ν α Z⁻¹).PosDef := by
    rw [hKZ]
    exact hdec
  obtain ⟨hstrict, hstable⟩ :=
    posDef_sub_and_mem_matrixKInverseStableDomain_of_ordered_transform_decrease ν hν α hα
      Y Zsa hY hgapY hZ.1 hsec
  exact ⟨Zsa, hstrict, hstable, hKZ⟩

end NLAlib

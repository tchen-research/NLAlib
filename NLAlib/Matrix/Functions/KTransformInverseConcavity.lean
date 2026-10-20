import NLAlib.Matrix.Functions.KTransformInverseConvexity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-! # Actual operator concavity of the inverse-variable K transform

The positive inverse is operator convex on every genuine sample gap.
Congruence by each Hermitian sample and the actual integral derive the
opposite operator inequality for the native inverse-variable K transform.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual inverse-resolvent sandwich is integrable on the original
compact sample support whenever its actual denominators are positive. -/
theorem integrable_matrixKInverseSandwich
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (Y : M) (hgap : ∀ T ∈ ν.support, (Y + T.val).PosDef) :
    Integrable (fun T : selfAdjoint M => T.val * (Y + T.val)⁻¹ * T.val) ν := by
  have hc : ContinuousOn (fun T : selfAdjoint M => T.val * (Y + T.val)⁻¹ * T.val)
      ν.support := by
    intro T hT
    have hi : ContinuousAt (fun U : selfAdjoint M => (Y + U.val)⁻¹) T :=
      (hasFDerivAt_matrixInverse (Y + T.val) (hgap T hT).isUnit).continuousAt.comp
        (f := fun U : selfAdjoint M => Y + U.val)
        (continuous_const.add continuous_subtype_val).continuousAt
    exact ((continuous_subtype_val.continuousAt.mul hi).mul
      continuous_subtype_val.continuousAt).continuousWithinAt
  have hi := hc.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn, hre] at hi

private theorem inverse_concavity_sum_gap
    (Y Z T : M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hY : (Y + T).PosDef) (hZ : (Z + T).PosDef) :
    (a • Y + b • Z + T).PosDef ∧
      (a • Y + b • Z + T)⁻¹ ≤ a • (Y + T)⁻¹ + b • (Z + T)⁻¹ := by
  have he : a • (Y + T) + b • (Z + T) = a • Y + b • Z + T := by
    calc
      _ = a • Y + b • Z + (a + b) • T := by module
      _ = _ := by rw [hab, one_smul]
  have hp := CStarAlgebra.convexOn_ringInverse.1
    hY.isStrictlyPositive hZ.isStrictlyPositive ha hb hab
  have hi := CStarAlgebra.convexOn_ringInverse.2
    hY.isStrictlyPositive hZ.isStrictlyPositive ha hb hab
  rw [he] at hp hi
  exact ⟨hp.posDef, by simpa only [← Matrix.nonsing_inv_eq_ringInverse] using hi⟩

/-- Convex combinations of actual positive inverse variables preserve
every actual sample gap. This is a geometric domain statement. -/
theorem posDef_add_samples_of_convex_combination
    (ν : Measure (selfAdjoint M)) (Y Z : M)
    (hY : Y.PosDef) (hZ : Z.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • Y + b • Z).PosDef ∧
      ∀ T ∈ ν.support, (a • Y + b • Z + T.val).PosDef := by
  have hp := inverse_concavity_sum_gap Y Z 0 ha hb hab
    (by simpa using hY) (by simpa using hZ)
  exact ⟨by simpa only [add_zero] using hp.1,
    fun T hT => (inverse_concavity_sum_gap Y Z T.val ha hb hab (hgapY T hT) (hgapZ T hT)).1⟩

/-- The true inverse-variable K transform is operator concave on its
positive sample-gap domain, including indefinite and singular samples.
The inequality is derived from operator convexity of the actual inverse
and the genuine sample integral.
Source: Montanari--Saeed (2026), inverse-variable form of equation (8).
atlas: block-wishart-log-potential (partial) -/
theorem smul_add_smul_matrixKTransform_inverse_le
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (Y Z : M) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • matrixKTransform ν α Y⁻¹ + b • matrixKTransform ν α Z⁻¹ ≤
      matrixKTransform ν α (a • Y + b • Z)⁻¹ := by
  let W := a • Y + b • Z
  obtain ⟨hW, hgapW⟩ := posDef_add_samples_of_convex_combination
    ν Y Z hY hZ hgapY hgapZ ha hb hab
  have hiY := integrable_matrixKInverseSandwich ν hν Y hgapY
  have hiZ := integrable_matrixKInverseSandwich ν hν Z hgapZ
  have hiW := integrable_matrixKInverseSandwich ν hν W hgapW
  have hiYa : Integrable (fun T : selfAdjoint M => a • (T.val * (Y + T.val)⁻¹ * T.val)) ν := hiY.smul a
  have hiZb : Integrable (fun T : selfAdjoint M => b • (T.val * (Z + T.val)⁻¹ * T.val)) ν := hiZ.smul b
  have hI : (∫ T : selfAdjoint M, T.val * (W + T.val)⁻¹ * T.val ∂ν) ≤
      a • (∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν) +
        b • (∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν) := by
    rw [← integral_smul, ← integral_smul, ← integral_add hiYa hiZb]
    apply integral_mono_ae hiW (hiYa.add hiZb)
    filter_upwards [ν.support_mem_ae] with T hT
    have hTH : T.val.IsHermitian := T.property
    have hinv := (inverse_concavity_sum_gap Y Z T.val ha hb hab (hgapY T hT) (hgapZ T hT)).2
    have hp := (Matrix.le_iff.mp hinv).mul_mul_conjTranspose_same T.val
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hTH.eq, W, Pi.add_apply] using hp
  rw [matrixKTransform_inverse_eq ν hν α Y hY hgapY,
    matrixKTransform_inverse_eq ν hν α Z hZ hgapZ,
    matrixKTransform_inverse_eq ν hν α W hW hgapW]
  let E := ∫ T : selfAdjoint M, T.val ∂ν
  let RY := ∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν
  let RZ := ∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν
  let RW := ∫ T : selfAdjoint M, T.val * (W + T.val)⁻¹ * T.val ∂ν
  have hE : a • E + b • E = E := by rw [← add_smul, hab, one_smul]
  change a • (E - RY - α⁻¹ • Y) + b • (E - RZ - α⁻¹ • Z) ≤ E - RW - α⁻¹ • W
  calc
    _ = (a • E + b • E) - (a • RY + b • RZ) - α⁻¹ • W := by dsimp only [W]; module
    _ = E - (a • RY + b • RZ) - α⁻¹ • W := by rw [hE]
    _ ≤ E - RW - α⁻¹ • W := sub_le_sub_right (sub_le_sub_left hI E) _

end NLAlib

import NLAlib.Matrix.Functions.WeightedInverseRay
import NLAlib.Matrix.Functions.KTransformCalculus
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.Analysis.Convex.PathConnected

/-!
# Actual inverse-variable stable K-domain certificate rays

The source inverse-variable stability map is an actual matrix integral.
Whitening the certificate proves that its value decreases along the
certificate's positive ray. Source: Montanari--Saeed (2026), Lemma 9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal inverse-variable stability expression of source (147).
Its sample matrices and probability law are genuine source objects. -/
def matrixKInverseStability
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (Y B : Matrix n n ℂ) : Matrix n n ℂ :=
  α • ∫ T, T.val*(Y+T.val)⁻¹*B*(Y+T.val)⁻¹*T.val ∂ν

/-- The source's actual inverse-variable stable domain, defined by positive
matrices, actual support gaps, and an actual positive integral defect. -/
def matrixKInverseStableDomain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ) :
    Set (selfAdjoint (Matrix n n ℂ)) :=
  {Y | Y.val.PosDef ∧ (∀ T ∈ ν.support, (Y.val+T.val).PosDef) ∧
    ∃ B : Matrix n n ℂ, B.PosDef ∧ (B-matrixKInverseStability ν α Y.val B).PosDef}

private theorem continuousOn_inverseStabilityKernel
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (Y B : Matrix n n ℂ)
    (hgap : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) =>
      T.val*(Y+T.val)⁻¹*B*(Y+T.val)⁻¹*T.val) ν.support := by
  intro T hT
  have hi : ContinuousAt (fun T : selfAdjoint (Matrix n n ℂ) => (Y+T.val)⁻¹) T :=
    (hasFDerivAt_matrixInverse (Y+T.val) (hgap T hT).isUnit).continuousAt.comp
      (f := fun T : selfAdjoint (Matrix n n ℂ) => Y+T.val)
      (continuous_const.add continuous_subtype_val).continuousAt
  exact ((((continuous_subtype_val.continuousAt.mul hi).mul continuous_const.continuousAt).mul
    hi).mul continuous_subtype_val.continuousAt).continuousWithinAt

/-- The actual inverse-variable stability kernel is integrable from compact
support and actual support-only inverse gaps. -/
theorem integrable_matrixKInverseStability_kernel
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (Y B : Matrix n n ℂ)
    (hgap : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    Integrable (fun T => T.val*(Y+T.val)⁻¹*B*(Y+T.val)⁻¹*T.val) ν := by
  have hi := (continuousOn_inverseStabilityKernel ν Y B hgap).integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

/-- The actual inverse-variable stability map decreases along the positive
certificate ray, even when neither sample nor certificate commutes with the
base. The proof integrates the derived native weighted-inverse inequality.
Source: Montanari--Saeed (2026), Lemma 9, equations (149)--(153).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKInverseStability_add_smul_le
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) {α : ℝ} (hα : 0 ≤ α)
    (Y B : Matrix n n ℂ) (hB : B.PosDef)
    (hgap : ∀ T ∈ ν.support, (Y+T.val).PosDef) {t : ℝ} (ht : 0 ≤ t) :
    matrixKInverseStability ν α (Y+t•B) B ≤ matrixKInverseStability ν α Y B := by
  have hgap' (T) (hT : T ∈ ν.support) : (Y+t•B+T.val).PosDef := by
    have h := (hgap T hT).add_posSemidef (hB.posSemidef.smul ht)
    convert! h using 1; abel
  unfold matrixKInverseStability
  apply smul_le_smul_of_nonneg_left _ hα
  apply integral_mono_ae
    (integrable_matrixKInverseStability_kernel ν hν _ _ hgap')
    (integrable_matrixKInverseStability_kernel ν hν _ _ hgap)
  filter_upwards [ν.support_mem_ae] with T hT
  have hp := (Matrix.le_iff.mp
    (inv_mul_weight_inv_add_smul_le (Y+T.val) B (hgap T hT) hB ht)).mul_mul_conjTranspose_same T.val
  apply Matrix.le_iff.mpr
  convert! hp using 1
  have hTH : T.val.IsHermitian := T.property
  simp only [show (Y+T.val)+t•B=(Y+t•B)+T.val by abel,
    Matrix.mul_sub,Matrix.sub_mul,hTH.eq,Matrix.mul_assoc]

/-- A genuine positive inverse-variable certificate remains a certificate
everywhere along its own nonnegative ray. All original support gaps and
strict defects are retained.
Source: Montanari--Saeed (2026), Lemma 9, equation (148).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKInverseStableDomain_certificate_ray
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) {α : ℝ} (hα : 0 ≤ α)
    (Y : selfAdjoint (Matrix n n ℂ)) (hY : Y.val.PosDef)
    (hgap : ∀ T ∈ ν.support, (Y.val+T.val).PosDef)
    (B : Matrix n n ℂ) (hB : B.PosDef)
    (hdef : (B-matrixKInverseStability ν α Y.val B).PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    Y+t•(⟨B,hB.isHermitian⟩ : selfAdjoint (Matrix n n ℂ)) ∈
      matrixKInverseStableDomain ν α := by
  refine ⟨hY.add_posSemidef (hB.posSemidef.smul ht),?_,B,hB,?_⟩
  · intro T hT
    change (Y.val+t•B+T.val).PosDef
    have h := (hgap T hT).add_posSemidef (hB.posSemidef.smul ht)
    convert! h using 1; abel
  · have hle := matrixKInverseStability_add_smul_le ν hν hα Y.val B hB hgap ht
    have hp := hdef.add_posSemidef (Matrix.le_iff.mp hle)
    convert! hp using 1; abel

end NLAlib

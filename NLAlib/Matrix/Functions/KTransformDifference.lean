import NLAlib.Matrix.Functions.KTransformComplexCalculus
import NLAlib.Matrix.Functions.KTransformGeometry

/-!
# Actual two-point K-transform identities

The literal two-resolvent identity gives the actual K-transform difference
and its fixed-point equation. These are the algebraic inputs to global
injectivity on the stable domain; a derivative at one point alone does not
imply that global statement.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual K resolvents satisfy their exact two-point identity whenever
the two genuine solved denominators are invertible. -/
theorem matrixKResolvent_sub_matrixKResolvent
    (S Q T : Matrix n n ℂ) (hS : IsUnit (1 + S * T)) (hQ : IsUnit (1 + Q * T)) :
    matrixKResolvent S T - matrixKResolvent Q T =
      -(matrixKResolvent S T * (S-Q) * matrixKResolvent Q T) := by
  rw [matrixKResolvent, matrixKResolvent, ← Matrix.mul_sub,
    Matrix.inv_sub_inv ⟨fun _ => hQ,fun _ => hS⟩]
  have he : (1 + Q*T) - (1 + S*T) = -(S-Q)*T := by noncomm_ring
  rw [he]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- The actual K resolvent is integrable throughout the true inverse
domain, by compact support. No regularity off the support is needed. -/
theorem integrable_matrixKResolvent_of_mem_domain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) {S : Matrix n n ℂ}
    (hS : S ∈ matrixKTransformDomain ν) :
    Integrable (fun T => matrixKResolvent S T.val) ν := by
  have hc : ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val)
      ν.support := by
    intro T hT
    exact ((continuousAt_matrixKResolvent S T.val (hS.2 T hT)).comp
      (f := fun T : selfAdjoint (Matrix n n ℂ) => (S,T.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt).continuousWithinAt
  have hi := hc.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

/-- The difference of actual K-transforms is the genuine mixed-resolvent
integral plus the inverse difference pairing. All integrability is derived
from compact support and actual denominator invertibility. -/
theorem matrixKTransform_sub_matrixKTransform
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) {S Q : Matrix n n ℂ}
    (hS : S ∈ matrixKTransformDomain ν) (hQ : Q ∈ matrixKTransformDomain ν) :
    matrixKTransform ν α S - matrixKTransform ν α Q =
      α⁻¹ • (S⁻¹ * (S-Q) * Q⁻¹) -
        ∫ T, matrixKResolvent S T.val * (S-Q) * matrixKResolvent Q T.val ∂ν := by
  have hiS := integrable_matrixKResolvent_of_mem_domain ν hν hS
  have hiQ := integrable_matrixKResolvent_of_mem_domain ν hν hQ
  have hR : (∫ T, matrixKResolvent S T.val ∂ν) - (∫ T, matrixKResolvent Q T.val ∂ν) =
      -(∫ T, matrixKResolvent S T.val * (S-Q) * matrixKResolvent Q T.val ∂ν) := by
    rw [← integral_sub hiS hiQ, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [ν.support_mem_ae] with T hT
    exact matrixKResolvent_sub_matrixKResolvent S Q T.val (hS.2 T hT) (hQ.2 T hT)
  have hInv : S⁻¹ - Q⁻¹ = -(S⁻¹ * (S-Q) * Q⁻¹) := by
    rw [Matrix.inv_sub_inv ⟨fun _ => hQ.1,fun _ => hS.1⟩]
    rw [show Q-S = -(S-Q) by abel]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  calc
    matrixKTransform ν α S - matrixKTransform ν α Q =
        ((∫ T, matrixKResolvent S T.val ∂ν) - (∫ T, matrixKResolvent Q T.val ∂ν)) -
          α⁻¹ • (S⁻¹-Q⁻¹) := by unfold matrixKTransform; module
    _ = _ := by rw [hR,hInv,smul_neg]; abel

end NLAlib

import NLAlib.Matrix.Functions.KTransformGeometry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The actual integral K-transform stability operator and its congruence -/
noncomputable section
open MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The source's actual averaged stability operator on ambient matrices. Its
restriction to Hermitian matrices is a real linear self-adjoint cone map. -/
def matrixKStabilityMap (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  α • ∫ T, ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
    (matrixKCoefficient S T.val) (matrixKCoefficient S T.val) ∂ν

/-- The rational coefficient is the square-root congruence of the actual
resolvent, a useful continuity identity on the support. -/
theorem matrixKCoefficient_eq_sqrt_congruence (S T : Matrix n n ℂ) (hS : S.PosDef) :
    matrixKCoefficient S T = cfc Real.sqrt S * matrixKResolvent S T * cfc Real.sqrt S := by
  let Q := cfc Real.sqrt S
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  have hQR : Q * R = 1 := cfc_sqrt_mul_inv_sqrt hS
  have hRQ : R * Q = 1 := cfc_inv_sqrt_mul_sqrt hS
  rw [matrixKResolvent_eq_inv_sqrt_congruence S T hS]
  change _ = Q * (R * matrixKCoefficient S T * R) * Q
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul,
    Matrix.mul_assoc, hRQ, Matrix.mul_one]

private theorem continuousOn_kResolvent_support (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    (S : Matrix n n ℂ) (hden : ∀ T ∈ ν.support, IsUnit (1 + S * T.val)) :
    ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val) ν.support := by
  intro T hT
  have hc : ContinuousAt (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val) T :=
    (continuousAt_matrixKResolvent S T.val (hden T hT)).comp
      (f := fun T : selfAdjoint (Matrix n n ℂ) => (S,T.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt
  exact hc.continuousWithinAt

/-- Both actual CLM integrands are integrable from the source hypotheses alone. -/
theorem integrable_matrixK_kernels (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    Integrable (fun T => matrixKResolventDeriv S T.val) ν ∧
    Integrable (fun T => ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
      (matrixKCoefficient S T.val) (matrixKCoefficient S T.val)) ν := by
  have hden := fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT)
  have hR := continuousOn_kResolvent_support ν S hden
  have hC : ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKCoefficient S T.val) ν.support := by
    simp_rw [matrixKCoefficient_eq_sqrt_congruence S _ hS]
    exact (continuous_const.continuousOn.mul hR).mul continuous_const.continuousOn
  have hRC := ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous.comp_continuousOn hR).clm_apply hR
  have hCC := ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous.comp_continuousOn hC).clm_apply hC
  have hiR := hRC.neg.integrableOn_compact (μ := ν) hν
  have hiC := hCC.integrableOn_compact (μ := ν) hν
  have heq : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rw [IntegrableOn, heq] at hiR hiC
  exact ⟨hiR,hiC⟩

/-- Evaluation of the actual derivative integral yields the exact source
formula, with the left and right resolvents written as in equation (F20).
atlas: matrix-k-transform-stability (partial) -/
theorem matrixKTransformDeriv_apply (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) (Δ : Matrix n n ℂ) :
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (S⁻¹ * Δ * S⁻¹) -
      ∫ T, T.val * (1 + S * T.val)⁻¹ * Δ * (1 + T.val * S)⁻¹ * T.val ∂ν := by
  have hi := (integrable_matrixK_kernels ν hν S hS hgap).1
  unfold matrixKTransformDeriv
  rw [add_apply, smul_apply, ContinuousLinearMap.integral_apply hi Δ]
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  rw [integral_neg]
  have he : (∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν) =
      ∫ T, T.val * (1 + S * T.val)⁻¹ * Δ * (1 + T.val * S)⁻¹ * T.val ∂ν := by
    apply integral_congr_ae
    filter_upwards [ν.support_mem_ae] with T hT
    have hHerm : T.val.IsHermitian := T.property
    nth_rw 2 [matrixKResolvent_eq_right S T.val hS hHerm (hgap T hT)]
    unfold matrixKResolvent
    simp only [Matrix.mul_assoc]
  rw [he]
  abel

end NLAlib

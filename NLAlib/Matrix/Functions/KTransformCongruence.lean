import NLAlib.Matrix.Functions.KTransformIntegral

/-! # The actual averaged K-transform congruence identity -/
noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem matrixKTransformDeriv_apply_resolvent
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) (Δ : Matrix n n ℂ) :
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (S⁻¹ * Δ * S⁻¹) -
      ∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν := by
  have hi := (integrable_matrixK_kernels ν hν S hS hgap).1
  unfold matrixKTransformDeriv
  rw [add_apply, smul_apply, ContinuousLinearMap.integral_apply hi Δ]
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  rw [integral_neg]
  abel

/-- Evaluation of the genuine stability CLM is the actual source integral. -/
theorem matrixKStabilityMap_apply (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) (H : Matrix n n ℂ) :
    matrixKStabilityMap ν α S H = α • ∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν := by
  unfold matrixKStabilityMap
  rw [smul_apply, ContinuousLinearMap.integral_apply (integrable_matrixK_kernels ν hν S hS hgap).2 H]
  rfl

/-- The actual derivative is the inverse-square-root congruence of the actual
averaged stability operator. Source: user derivations, equation (F21).
atlas: matrix-k-transform-stability (partial) -/
theorem matrixKTransformDeriv_eq_congruence (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (hα : α ≠ 0)
    (S : Matrix n n ℂ) (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (Δ : Matrix n n ℂ) :
    let R := cfc (fun x => (Real.sqrt x)⁻¹) S
    let H := R * Δ * R
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (R * (H - matrixKStabilityMap ν α S H) * R) := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  let H := R * Δ * R
  change matrixKTransformDeriv ν α S Δ = α⁻¹ • (R * (H - matrixKStabilityMap ν α S H) * R)
  have hi0 := (integrable_matrixK_kernels ν hν S hS hgap).2
  have hi : Integrable (fun T => matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) ν := by
    simpa only [ContinuousLinearMap.mulLeftRight_apply] using hi0.apply_continuousLinearMap H
  let F := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) R R
  have htransport := F.integral_comp_comm hi
  change (∫ T, R * (matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) * R ∂ν) =
    R * (∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν) * R at htransport
  have hkernel : (∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν) =
      R * (∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν) * R := by
    rw [← htransport]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun T => by
      dsimp only
      rw [matrixKResolvent_eq_inv_sqrt_congruence S T.val hS]
      simp only [H,R,Matrix.mul_assoc]
  have hfirst : S⁻¹ * Δ * S⁻¹ = R * H * R := by
    rw [inv_eq_cfc_inv_sqrt_mul_self hS]
    simp only [R,H,Matrix.mul_assoc]
  rw [matrixKTransformDeriv_apply_resolvent ν hν α S hS hgap Δ,hkernel,hfirst,
    matrixKStabilityMap_apply ν hν α S hS hgap H]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    smul_sub,smul_smul,inv_mul_cancel₀ hα,one_smul]

omit [DecidableEq n] in
/-- Inverse-square-root congruence is self-adjoint for the actual real
Frobenius pairing. -/
theorem frobInner_hermitian_congruence (R A B : Matrix n n ℂ) (hR : R.IsHermitian) :
    frobInner A (R * B * R) = frobInner (R * A * R) B := by
  rw [frobInner_eq_trace,frobInner_eq_trace,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul,hR.eq]
  congr 1
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (Aᴴ * R * B) R

/-- The source's actual Frobenius quadratic identity follows from the actual
derivative congruence, without changing the derivative or inner product.
atlas: matrix-k-transform-stability (partial) -/
theorem frobInner_matrixKTransformDeriv (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (hα : α ≠ 0)
    (S : Matrix n n ℂ) (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (Δ : Matrix n n ℂ) :
    let R := cfc (fun x => (Real.sqrt x)⁻¹) S
    let H := R * Δ * R
    frobInner Δ (matrixKTransformDeriv ν α S Δ) = α⁻¹ * frobInner H (H - matrixKStabilityMap ν α S H) := by
  rw [matrixKTransformDeriv_eq_congruence ν hν α hα S hS hgap Δ,frobInner_smul_right,
    frobInner_hermitian_congruence]
  exact cfc_predicate _ _

end NLAlib

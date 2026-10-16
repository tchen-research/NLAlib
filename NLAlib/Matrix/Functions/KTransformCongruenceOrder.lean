import NLAlib.Matrix.Functions.KTransformHilbert

/-! # Invertible whitening transports the actual K derivative order tests -/
noncomputable section
open MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square-root congruence undoes inverse-square-root congruence. -/
theorem sqrt_invSqrt_congruence (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    cfc Real.sqrt S * (cfc (fun x => (Real.sqrt x)⁻¹) S * X *
      cfc (fun x => (Real.sqrt x)⁻¹) S) * cfc Real.sqrt S = X := by
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,cfc_sqrt_mul_inv_sqrt hS,Matrix.one_mul,
    Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hS,Matrix.mul_one]

/-- Inverse-square-root congruence undoes square-root congruence. -/
theorem invSqrt_sqrt_congruence (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    cfc (fun x => (Real.sqrt x)⁻¹) S * (cfc Real.sqrt S * X * cfc Real.sqrt S) *
      cfc (fun x => (Real.sqrt x)⁻¹) S = X := by
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hS,Matrix.one_mul,
    Matrix.mul_assoc,cfc_sqrt_mul_inv_sqrt hS,Matrix.mul_one]

/-- The inverse square root is an actual invertible Hermitian matrix. -/
theorem isUnit_cfc_invSqrt (S : Matrix n n ℂ) (hS : S.PosDef) :
    IsUnit (cfc (fun x => (Real.sqrt x)⁻¹) S) :=
  ⟨⟨_,cfc Real.sqrt S,cfc_inv_sqrt_mul_sqrt hS,cfc_sqrt_mul_inv_sqrt hS⟩,rfl⟩

/-- Strict matrix positivity is unchanged by inverse-square-root congruence. -/
theorem posDef_invSqrt_congruence_iff (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    (cfc (fun x => (Real.sqrt x)⁻¹) S * X * cfc (fun x => (Real.sqrt x)⁻¹) S).PosDef ↔ X.PosDef := by
  have hR : (cfc (fun x => (Real.sqrt x)⁻¹) S).IsHermitian := cfc_predicate _ _
  simpa only [Matrix.star_eq_conjTranspose,hR.eq] using
    Matrix.IsUnit.posDef_star_right_conjugate_iff (isUnit_cfc_invSqrt S hS) (x:=X)

/-- Strict matrix positivity is unchanged by square-root congruence. -/
theorem posDef_sqrt_congruence_iff (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    (cfc Real.sqrt S * X * cfc Real.sqrt S).PosDef ↔ X.PosDef := by
  have hQ : (cfc Real.sqrt S).IsHermitian := cfc_predicate _ _
  have hi : IsUnit (cfc Real.sqrt S) :=
    ⟨⟨_,_,cfc_sqrt_mul_inv_sqrt hS,cfc_inv_sqrt_mul_sqrt hS⟩,rfl⟩
  simpa only [Matrix.star_eq_conjTranspose,hQ.eq] using
    Matrix.IsUnit.posDef_star_right_conjugate_iff hi (x:=X)

omit [Fintype n] [DecidableEq n] in
/-- Positive scalar multiplication preserves and reflects strict positivity. -/
theorem posDef_real_smul_iff (a : ℝ) (ha : 0<a) (X : Matrix n n ℂ) :
    (a•X).PosDef ↔ X.PosDef := by
  constructor
  · intro h
    have hh := h.smul (inv_pos.mpr ha)
    simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt ha),one_smul] using hh
  · exact fun h => h.smul ha

/-- The derivative's strict-positive output condition is exactly the strict
supersolution gap after invertible whitening. -/
theorem posDef_matrixKTransformDeriv_iff
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) (Δ : Matrix n n ℂ) :
    (matrixKTransformDeriv ν α S Δ).PosDef ↔
      (cfc (fun x => (Real.sqrt x)⁻¹) S * Δ * cfc (fun x => (Real.sqrt x)⁻¹) S -
        matrixKStabilityMap ν α S (cfc (fun x => (Real.sqrt x)⁻¹) S * Δ *
          cfc (fun x => (Real.sqrt x)⁻¹) S)).PosDef := by
  rw [matrixKTransformDeriv_eq_congruence ν hν α (ne_of_gt hα) S hS hgap Δ]
  rw [posDef_real_smul_iff _ (inv_pos.mpr hα),posDef_invSqrt_congruence_iff S hS]

end NLAlib

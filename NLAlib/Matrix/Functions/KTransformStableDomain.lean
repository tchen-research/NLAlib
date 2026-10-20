import NLAlib.Matrix.Functions.KTransformStableConnected
import NLAlib.Matrix.Functions.KTransformStability

/-!
# Connectedness of the actual original stable K-domain

Actual inversion transports the inverse-variable integral certificates to
the original derivative tests. All certificate equivalences are proved
using the actual K derivative. Source: Montanari--Saeed (2026), Lemma 9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual original source stable region uses the true K derivative
and its strict Frobenius quadratic test on Hermitian directions. -/
def matrixKStableDomain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ) : Set (Matrix n n ℂ) :=
  {S | S.PosDef ∧ (∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) ∧
    ∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)}

private theorem inverseStability_defect_eq_smul_derivative
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : α≠0)
    (S B : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    S⁻¹*B*S⁻¹-matrixKInverseStability ν α S⁻¹ (S⁻¹*B*S⁻¹) =
      α • matrixKTransformDeriv ν α S B := by
  rw [matrixKTransformDeriv_apply ν hν α S hS hgap B]
  simp only [smul_sub,smul_smul,mul_inv_cancel₀ hα,one_smul,matrixKInverseStability]
  apply congrArg (fun X : Matrix n n ℂ => S⁻¹*B*S⁻¹-α•X)
  apply integral_congr_ae
  apply ae_of_all
  intro T
  dsimp only
  have hleft : 1+S*T.val=S*(S⁻¹+T.val) := by
    rw [Matrix.mul_add,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  have hright : 1+T.val*S=(S⁻¹+T.val)*S := by
    rw [Matrix.add_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  rw [hleft,hright,Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

private theorem posDef_sandwich (S B : Matrix n n ℂ) (hS : S.PosDef) (hB : B.PosDef) :
    (S*B*S).PosDef := by
  simpa only [Matrix.star_eq_conjTranspose,hS.isHermitian.eq] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff hS.isUnit (x := B)).mpr hB

private theorem derivative_witness_iff_inverse_witness
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef) ↔
      ∃ C : Matrix n n ℂ, C.PosDef ∧ (C-matrixKInverseStability ν α S⁻¹ C).PosDef := by
  constructor
  · rintro ⟨B,hB,hD⟩
    refine ⟨S⁻¹*B*S⁻¹,posDef_sandwich S⁻¹ B hS.inv hB,?_⟩
    rw [inverseStability_defect_eq_smul_derivative ν hν α hα.ne' S B hS hgap]
    exact (posDef_real_smul_iff α hα _).mpr hD
  · rintro ⟨C,hC,hdef⟩
    let B := S*C*S
    have hcan : S⁻¹*B*S⁻¹=C := by
      dsimp [B]
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit),
        Matrix.one_mul,Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit),Matrix.mul_one]
    refine ⟨B,posDef_sandwich S C hS hC,?_⟩
    apply (posDef_real_smul_iff α hα _).mp
    rw [← inverseStability_defect_eq_smul_derivative ν hν α hα.ne' S B hS hgap,hcan]
    exact hdef

private theorem quadratic_pos_iff_inverse_witness [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
      ∃ C : Matrix n n ℂ, C.PosDef ∧ (C-matrixKInverseStability ν α S⁻¹ C).PosDef := by
  rw [matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS hgap,
    matrixKTransform_norm_iff_supersolution ν hν α hα S hS hgap,
    matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S hS hgap]
  exact derivative_witness_iff_inverse_witness ν hν α hα S hS hgap

/-- The original source stable region is exactly the actual inversion image
of the genuine inverse-variable stable region. All strict Frobenius tests
and actual integral certificate equivalences are derived.
Source: Montanari--Saeed (2026), Lemma 9, equations (145)--(147).
atlas: block-wishart-variational-edges (partial) -/
theorem image_inverse_matrixKInverseStableDomain [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α) :
    (fun Y : selfAdjoint (Matrix n n ℂ) => Y.val⁻¹) '' matrixKInverseStableDomain ν α =
      matrixKStableDomain ν α := by
  ext S
  constructor
  · rintro ⟨Y,⟨hY,hgap,hw⟩,rfl⟩
    have hYY : Y.val⁻¹⁻¹=Y.val :=
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)
    refine ⟨hY.inv,?_,?_⟩
    · simpa only [hYY] using hgap
    · apply (quadratic_pos_iff_inverse_witness ν hν α hα Y.val⁻¹ hY.inv
        (by simpa only [hYY] using hgap)).mpr
      simpa only [hYY] using hw
  · rintro ⟨hS,hgap,hquad⟩
    let Y : selfAdjoint (Matrix n n ℂ) := ⟨S⁻¹,hS.inv.isHermitian⟩
    refine ⟨Y,⟨hS.inv,hgap,?_⟩,?_⟩
    · exact (quadratic_pos_iff_inverse_witness ν hν α hα S hS hgap).mp hquad
    · exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)

/-- The actual source stable K-domain is connected. The source's original
strict derivative geometry is retained, and the connectedness proof uses
actual inversion of the derived certificate rays and common convex core.
Source: Montanari--Saeed (2026), Lemma 9.
atlas: block-wishart-variational-edges (partial) -/
theorem isConnected_matrixKStableDomain [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α) :
    IsConnected (matrixKStableDomain ν α) := by
  have hc : ContinuousOn (fun Y : selfAdjoint (Matrix n n ℂ) => Y.val⁻¹)
      (matrixKInverseStableDomain ν α) := by
    intro Y hY
    exact ((hasFDerivAt_matrixInverse Y.val hY.1.isUnit).continuousAt.comp
      (f := fun Y : selfAdjoint (Matrix n n ℂ) => Y.val)
      continuous_subtype_val.continuousAt).continuousWithinAt
  have hh := (isConnected_matrixKInverseStableDomain ν hν hα.le).image _ hc
  rwa [image_inverse_matrixKInverseStableDomain ν hν α hα] at hh

end NLAlib

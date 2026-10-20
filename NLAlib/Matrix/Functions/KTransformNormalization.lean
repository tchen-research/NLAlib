import NLAlib.Matrix.Functions.KTransformUpperBounds

/-! # Native K-branch normalization at imaginary infinity

The actual nonlinear equation bounds the normalization error through its
true sample resolvent average. No linear Dyson equation is substituted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem normalization_neg_inverse_involutive (S : M) (hS : IsUnit S) :
    -(-S⁻¹)⁻¹=S := by
  have hi : (-S⁻¹)⁻¹= -S := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.neg_mul,Matrix.mul_neg,neg_neg,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
  rw [hi,neg_neg]

/-- The actual averaged rational kernel of a genuine K solution is
bounded using the sample support and the target imaginary coercivity.
Source: Montanari--Saeed (2026), Appendix A, normalization in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_integral_matrixKResolvent_of_solution_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z S : M) (hS : (imaginaryPart S : M).PosDef)
    (hK : matrixKTransform ν α S=Z) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hZ : η•(1 : M)≤α•(imaginaryPart Z : M)) :
    specNorm (∫ T,matrixKResolvent S T.val ∂ν)≤R+R^2*η⁻¹ := by
  let X := -S⁻¹
  have hXpos : (imaginaryPart X : M).PosDef := posDef_imaginaryPart_neg_matrixInverse S hS
  have hXcoercive : η•(1 : M)≤(imaginaryPart X : M) := hZ.trans
    (matrixKTransform_solution_inverse_variable ν hν α hα Z S hS hK).2
  have hinvol : -X⁻¹=S := normalization_neg_inverse_involutive S
    (Matrix.isUnit_of_posDef_imaginaryPart hS)
  have hpt : ∀ᵐ T : selfAdjoint M ∂ν, ‖matrixKResolvent S T.val‖≤R+R^2*η⁻¹ := by
    filter_upwards [ν.support_mem_ae] with T hT
    have hTN : ‖T.val‖≤R := by simpa only [specNorm_eq_norm] using hbound T hT
    have hRN : ‖(X-T.val)⁻¹‖≤η⁻¹ := by
      simpa only [specNorm_eq_norm] using
        specNorm_inverseVariable_resolvent_le_inv X T.val T.property η hη hXcoercive
    have hR0 : 0≤R := (norm_nonneg T.val).trans hTN
    have hker : matrixKResolvent S T.val=T.val+T.val*(X-T.val)⁻¹*T.val := by
      rw [← hinvol]
      exact matrixKResolvent_neg_inverse_eq X T.val hXpos T.property
    rw [hker]
    calc
      _ ≤ ‖T.val‖+‖T.val*(X-T.val)⁻¹*T.val‖ := norm_add_le _ _
      _ ≤ ‖T.val‖+‖T.val‖*‖(X-T.val)⁻¹‖*‖T.val‖ :=
        add_le_add le_rfl ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      _ ≤ R+R*η⁻¹*R := by gcongr
      _ = _ := by ring
  simpa only [specNorm_eq_norm,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) hpt

/-- Multiplication of the original nonlinear K equation gives its exact
normalization error identity. This uses the genuine rational average,
not a fixed linear self-energy map.
Source: Montanari--Saeed (2026), Appendix A, Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_normalization_error_identity
    (ν : Measure (selfAdjoint M)) (α : ℝ) (hα : α≠0) (z : ℂ) (S : M)
    (hS : IsUnit S) (hK : matrixKTransform ν α S=z•1) :
    z•(α•S)+1=α•((∫ T,matrixKResolvent S T.val ∂ν)*S) := by
  have he := congrArg (fun Y : M => α•(Y*S)) hK
  rw [matrixKTransform,Matrix.sub_mul,Matrix.smul_mul,smul_sub,smul_smul,
    mul_inv_cancel₀ hα,one_smul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),
    Matrix.smul_mul,Matrix.one_mul] at he
  rw [← smul_comm α z S]
  rw [← he]
  abel

/-- The actual nonlinear K equation gives a quantitative normalization
error controlled solely by native sample and target coercivity bounds.
Source: Montanari--Saeed (2026), Appendix A, Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_matrixKTransform_normalization_error_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (z : ℂ) (S : M) (hS : (imaginaryPart S : M).PosDef)
    (hK : matrixKTransform ν α S=z•1) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hZ : η•(1 : M)≤α•(imaginaryPart (z•(1 : M)) : M)) :
    specNorm (z•(α•S)+1)≤α*((R+R^2*η⁻¹)*η⁻¹) := by
  have hI := specNorm_integral_matrixKResolvent_of_solution_le ν hν α hα
    (z•1) S hS hK η R hη hbound hZ
  have hSN := specNorm_of_matrixKTransform_solution_le_inv ν hν α hα (z•1) S hS hK η hη hZ
  rw [matrixKTransform_normalization_error_identity ν α hα.ne' z S
    (Matrix.isUnit_of_posDef_imaginaryPart hS) hK,specNorm_eq_norm,norm_smul,
    Real.norm_of_nonneg hα.le]
  have hIN : ‖∫ T,matrixKResolvent S T.val ∂ν‖≤R+R^2*η⁻¹ := by
    simpa only [specNorm_eq_norm] using hI
  have hSNorm : ‖S‖≤η⁻¹ := by simpa only [specNorm_eq_norm] using hSN
  exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
    (mul_le_mul hIN hSNorm (norm_nonneg S) ((norm_nonneg _).trans hIN))) hα.le

/-- Every genuine upper-half-plane K solution has the exact mass
normalization `iy (α S(iy)) → -I`, derived from its actual nonlinear
equation and compact sample law. No normalization, representing measure,
or linear Dyson equation is assumed.
Source: Montanari--Saeed (2026), Lemma 1; Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem tendsto_mul_I_smul_matrixKTransform_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1) :
    Tendsto (fun y : ℝ => ((y : ℂ)*Complex.I)•(α•F ((y : ℂ)*Complex.I)))
      atTop (𝓝 (-1)) := by
  obtain ⟨R,hR⟩ := hν.isBounded.exists_norm_le
  have hbound : ∀ T ∈ ν.support, specNorm T.val≤R := by
    intro T hT
    simpa only [specNorm_eq_norm,← AddSubgroup.norm_coe] using hR T hT
  have hinv : Tendsto (fun y : ℝ => (α*y)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hα tendsto_id)
  have hlimit : Tendsto (fun y : ℝ => α*((R+R^2*(α*y)⁻¹)*(α*y)⁻¹))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_const_nhds.add (hinv.const_mul (R^2))).mul hinv).const_mul α
  have hnorm : Tendsto (fun y : ℝ => ‖((y : ℂ)*Complex.I)•
      (α•F ((y : ℂ)*Complex.I))+1‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlimit
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hz : 0<((y : ℂ)*Complex.I).im := by simpa using hy
    have hη : 0<α*y := mul_pos hα hy
    have hZ : (α*y)•(1 : M)≤α•(imaginaryPart (((y : ℂ)*Complex.I)•(1 : M)) : M) := by
      have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
      simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one,smul_smul]
    exact specNorm_matrixKTransform_normalization_error_le ν hν α hα
      ((y : ℂ)*Complex.I) (F _) (hF _ hz).1 (hF _ hz).2 (α*y) R hη hbound hZ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_neg_eq_add] using hnorm

end NLAlib

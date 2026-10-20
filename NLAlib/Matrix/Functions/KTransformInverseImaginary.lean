import NLAlib.Matrix.Functions.KTransformUpperBounds

/-! # The exact imaginary equation of the native inverse-variable map

The nonlinear resolvent sandwich transports the actual positive
imaginary part through a true completely positive integral kernel.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem inverseImaginary_integrable_continuous
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    {f : selfAdjoint M → M} (hf : Continuous f) : Integrable f ν := by
  have hi := hf.continuousOn.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

private theorem inverseImaginary_unit (X T : M)
    (hX : (imaginaryPart X : M).PosDef) (hT : T.IsHermitian) : IsUnit (X-T) := by
  apply Matrix.isUnit_of_posDef_imaginaryPart
  simpa only [map_sub,hT.isSelfAdjoint.imaginaryPart,sub_zero] using hX

private theorem inverseImaginary_continuous_resolvent (X : M)
    (hX : (imaginaryPart X : M).PosDef) :
    Continuous (fun T : selfAdjoint M => (X-T.val)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (hasFDerivAt_matrixInverse (X-T.val)
    (inverseImaginary_unit X T.val hX T.property)).continuousAt.comp
      (f := fun T : selfAdjoint M => X-T.val)
      (continuous_const.sub continuous_subtype_val).continuousAt

private theorem inverseImaginary_sandwich (X T : M)
    (hX : (imaginaryPart X : M).PosDef) (hT : T.IsHermitian) :
    (imaginaryPart (T*(X-T)⁻¹*T) : M)=
      -(T*((X-T)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T)⁻¹*T) := by
  have hu := inverseImaginary_unit X T hX hT
  have hm : (X-T)*(-(X-T)⁻¹)= -1 := by
    rw [Matrix.mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  have hi := Matrix.imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one hm
  have him : (imaginaryPart (X-T) : M)=(imaginaryPart X : M) := by
    rw [map_sub,hT.isSelfAdjoint.imaginaryPart,sub_zero]
  simp only [map_neg,NegMemClass.coe_neg,Matrix.conjTranspose_neg,
    Matrix.neg_mul,Matrix.mul_neg,neg_neg,him] at hi
  have hs : (imaginaryPart (T*(X-T)⁻¹*T) : M)=
      T*(imaginaryPart ((X-T)⁻¹) : M)*T := by
    simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul,hT.eq,Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    noncomm_ring
  have hIm : (imaginaryPart ((X-T)⁻¹) : M)=
      -(((X-T)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T)⁻¹) := neg_eq_iff_eq_neg.mp hi
  rw [hs,hIm]
  simp only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]

/-- The actual nonlinear inverse-variable map has this exact positive
imaginary-part equation. The integral is derived from the genuine
Hermitian sample resolvents, including singular and indefinite samples.
Source: Montanari--Saeed (2026), Lemma 1, exterior Stieltjes-law argument.
atlas: block-wishart-variational-edges (partial) -/
theorem imaginaryPart_matrixKInverseVariableMap
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (Z X : M) (hX : (imaginaryPart X : M).PosDef) :
    (imaginaryPart (matrixKInverseVariableMap ν α Z X) : M)=
      α•(imaginaryPart Z : M)+
      α•(∫ T : selfAdjoint M,
        T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val ∂ν) := by
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  have hL (Y : M) : L Y=(imaginaryPart Y : M) := rfl
  let f (T : selfAdjoint M) := T.val*(X-T.val)⁻¹*T.val
  have hiT : Integrable (fun T : selfAdjoint M => T.val) ν :=
    inverseImaginary_integrable_continuous ν hν continuous_subtype_val
  have hif : Integrable f ν := inverseImaginary_integrable_continuous ν hν
    ((continuous_subtype_val.mul (inverseImaginary_continuous_resolvent X hX)).mul
      continuous_subtype_val)
  have hmean : L (∫ T : selfAdjoint M,T.val ∂ν)=0 := by
    rw [← L.integral_comp_comm hiT]
    have hz (T : selfAdjoint M) : L T.val=0 := by
      rw [hL]
      have hh : T.val.IsHermitian := T.property
      simp only [hh.isSelfAdjoint.imaginaryPart,ZeroMemClass.coe_zero]
    simp_rw [hz]
    exact integral_zero _ _
  have hIp : L (∫ T,f T ∂ν)=
      -(∫ T : selfAdjoint M,
        T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val ∂ν) := by
    rw [← L.integral_comp_comm hif]
    have hp (T : selfAdjoint M) : L (f T)=
        -(T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val) :=
      inverseImaginary_sandwich X T.val hX T.property
    simp_rw [hp]
    rw [integral_neg]
  change L (α•(Z-(∫ T : selfAdjoint M,T.val ∂ν)-(∫ T,f T ∂ν)))=_
  rw [map_smul,map_sub,map_sub,hmean,hIp,sub_zero,sub_neg_eq_add,smul_add,hL]

/-- A genuine uniform sample-resolvent bound controls the imaginary
part of the actual inverse-variable K map. This is the native integral
estimate used to prove compact support, rather than a supplied bound on
the solution's imaginary part.
Source: Montanari--Saeed (2026), Lemma 1, exterior-law estimate.
atlas: block-wishart-variational-edges (partial) -/
theorem norm_imaginaryPart_matrixKInverseVariableMap_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0≤α) (Z X : M) (hX : (imaginaryPart X : M).PosDef)
    (R q : ℝ) (hR : 0≤R) (hq : 0≤q)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hres : ∀ T ∈ ν.support, ‖(X-T.val)⁻¹‖≤q) :
    ‖(imaginaryPart (matrixKInverseVariableMap ν α Z X) : M)‖≤
      α*‖(imaginaryPart Z : M)‖+α*(R^2*q^2*‖(imaginaryPart X : M)‖) := by
  have hpt : ∀ᵐ T : selfAdjoint M ∂ν,
      ‖T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val‖≤
        R^2*q^2*‖(imaginaryPart X : M)‖ := by
    filter_upwards [ν.support_mem_ae] with T hT
    have hTN : ‖T.val‖≤R := by simpa only [specNorm_eq_norm] using hbound T hT
    have hRN := hres T hT
    have hRS : ‖((X-T.val)⁻¹)ᴴ‖≤q := by
      simpa only [← Matrix.star_eq_conjTranspose,norm_star] using hRN
    calc
      _ ≤ ‖T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹‖*‖T.val‖ := norm_mul_le _ _
      _ ≤ ‖T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)‖*‖(X-T.val)⁻¹‖*‖T.val‖ := by
        gcongr; exact norm_mul_le _ _
      _ ≤ ‖T.val*((X-T.val)⁻¹)ᴴ‖*‖(imaginaryPart X : M)‖*‖(X-T.val)⁻¹‖*‖T.val‖ := by
        gcongr; exact norm_mul_le _ _
      _ ≤ ‖T.val‖*‖((X-T.val)⁻¹)ᴴ‖*‖(imaginaryPart X : M)‖*‖(X-T.val)⁻¹‖*‖T.val‖ := by
        gcongr; exact norm_mul_le _ _
      _ ≤ R*q*‖(imaginaryPart X : M)‖*q*R := by gcongr
      _ = _ := by ring
  have hI : ‖∫ T : selfAdjoint M,
      T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val ∂ν‖≤
        R^2*q^2*‖(imaginaryPart X : M)‖ := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := ν) hpt
  rw [imaginaryPart_matrixKInverseVariableMap ν hν α Z X hX]
  calc
    _ ≤ ‖α•(imaginaryPart Z : M)‖+‖α•(∫ T : selfAdjoint M,
        T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val ∂ν)‖ := norm_add_le _ _
    _ = α*‖(imaginaryPart Z : M)‖+α*‖∫ T : selfAdjoint M,
        T.val*((X-T.val)⁻¹)ᴴ*(imaginaryPart X : M)*(X-T.val)⁻¹*T.val ∂ν‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg hα]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hI hα)

end NLAlib

import NLAlib.Matrix.Functions.KTransformHalfPlaneDual

/-! # The genuine inverse-variable nonlinear K equation

The change of variable `M = -S⁻¹` converts the original rational K
equation into an additive resolvent equation. Its resolvents remain
uniformly coercive on every fixed positive imaginary half-space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem inverseVariable_integrable_continuous
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    {f : selfAdjoint M → M} (hf : Continuous f) : Integrable f ν := by
  have hi := hf.continuousOn.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn,hre] at hi

private theorem imaginaryPart_sub_hermitian (X T : M) (hT : T.IsHermitian) :
    (imaginaryPart (X-T) : M)=(imaginaryPart X : M) := by
  rw [map_sub,hT.isSelfAdjoint.imaginaryPart,sub_zero]

private theorem inverseVariable_sub_isUnit (X T : M)
    (hX : (imaginaryPart X : M).PosDef) (hT : T.IsHermitian) : IsUnit (X-T) := by
  apply Matrix.isUnit_of_posDef_imaginaryPart
  rwa [imaginaryPart_sub_hermitian X T hT]

/-- Negative inversion preserves the genuine matrix upper half-plane.
Source: Montanari--Saeed (2026), Appendix A, inverse-variable form of Lemma 10.
atlas: block-wishart-variational-edges (partial) -/
theorem posDef_imaginaryPart_neg_matrixInverse (X : M)
    (hX : (imaginaryPart X : M).PosDef) : (imaginaryPart (-X⁻¹) : M).PosDef := by
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hX
  have hXu : IsUnit (-X⁻¹) := (Matrix.isUnit_nonsing_inv_iff.mpr hu).neg
  have hXs : IsUnit (-X⁻¹)ᴴ := by
    simpa only [Matrix.star_eq_conjTranspose] using hXu.star
  have he : X*(-X⁻¹)= -1 := by
    rw [Matrix.mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  rw [Matrix.imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one he]
  have hp := (Matrix.IsUnit.posDef_star_right_conjugate_iff hXs).mpr hX
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using hp

/-- The actual rational K kernel becomes an ordinary Hermitian-sample
resolvent sandwich after genuine negative inversion. Singular samples
are included, and every inverse is justified by positive imaginary part.
Source: Montanari--Saeed (2026), Appendix A, equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKResolvent_neg_inverse_eq (X T : M)
    (hX : (imaginaryPart X : M).PosDef) (hT : T.IsHermitian) :
    matrixKResolvent (-X⁻¹) T=T+T*(X-T)⁻¹*T := by
  have hXu := Matrix.isUnit_of_posDef_imaginaryPart hX
  have hAu := inverseVariable_sub_isUnit X T hX hT
  have hD : 1+(-X⁻¹)*T=X⁻¹*(X-T) := by
    rw [Matrix.mul_sub,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hXu)]
    simp only [Matrix.neg_mul,sub_eq_add_neg]
  have hDi : (1+(-X⁻¹)*T)⁻¹=(X-T)⁻¹*X := by
    apply Matrix.inv_eq_right_inv
    calc
      _ = X⁻¹*((X-T)*(X-T)⁻¹)*X := by rw [hD]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hAu),
          Matrix.mul_one,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hXu)]
  rw [matrixKResolvent,hDi,Matrix.mul_assoc]
  calc
    _ = T*((X-T)⁻¹*((X-T)+T)) := congrArg (fun Y => T*((X-T)⁻¹*Y)) (by abel)
    _ = _ := by
      rw [Matrix.mul_add,Matrix.mul_add,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hAu),Matrix.mul_one]

private theorem continuous_inverseVariable_resolvent (X : M)
    (hX : (imaginaryPart X : M).PosDef) :
    Continuous (fun T : selfAdjoint M => (X-T.val)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (hasFDerivAt_matrixInverse (X-T.val)
    (inverseVariable_sub_isUnit X T.val hX T.property)).continuousAt.comp
      (f := fun T : selfAdjoint M => X-T.val)
      (continuous_const.sub continuous_subtype_val).continuousAt

/-- The actual nonlinear inverse-variable map for the original K equation.
Its definition uses the native sample law and ordinary matrix resolvents.
Source: the algebraic change `M = -S⁻¹` in Montanari--Saeed (2026), Lemma 1. -/
def matrixKInverseVariableMap (ν : Measure (selfAdjoint M)) (α : ℝ) (Z X : M) : M :=
  α • (Z-(∫ T, T.val ∂ν)-(∫ T, T.val*(X-T.val)⁻¹*T.val ∂ν))

/-- The inverse-variable equation is exactly the original native K
equation, with all sample integrability proved from compact support.
Source: Montanari--Saeed (2026), Appendix A, equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_neg_inverse_eq
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (X : M) (hX : (imaginaryPart X : M).PosDef) :
    matrixKTransform ν α (-X⁻¹)=
      (∫ T, T.val ∂ν)+(∫ T, T.val*(X-T.val)⁻¹*T.val ∂ν)+α⁻¹•X := by
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hX
  have hiX : (-X⁻¹)⁻¹= -X := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.neg_mul,Matrix.mul_neg,neg_neg,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  have hiT : Integrable (fun T : selfAdjoint M => T.val) ν :=
    inverseVariable_integrable_continuous ν hν continuous_subtype_val
  have hiR : Integrable (fun T : selfAdjoint M => T.val*(X-T.val)⁻¹*T.val) ν :=
    inverseVariable_integrable_continuous ν hν
      ((continuous_subtype_val.mul (continuous_inverseVariable_resolvent X hX)).mul
        continuous_subtype_val)
  have hker : (∫ T, matrixKResolvent (-X⁻¹) T.val ∂ν)=
      (∫ T, T.val ∂ν)+(∫ T, T.val*(X-T.val)⁻¹*T.val ∂ν) := by
    rw [← integral_add hiT hiR]
    apply integral_congr_ae
    exact ae_of_all _ fun T => matrixKResolvent_neg_inverse_eq X T.val hX T.property
  rw [matrixKTransform,hker,hiX,smul_neg,sub_neg_eq_add]

/-- A fixed point of the native inverse-variable map is precisely an
actual upper-half-plane K solution after negative inversion. No branch
or existence statement is used as a premise.
Source: Montanari--Saeed (2026), Lemma 1, equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_neg_inverse_eq_iff_fixedPoint
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : α≠0) (Z X : M) (hX : (imaginaryPart X : M).PosDef) :
    matrixKTransform ν α (-X⁻¹)=Z ↔ X=matrixKInverseVariableMap ν α Z X := by
  rw [matrixKTransform_neg_inverse_eq ν hν α X hX]
  constructor
  · intro h
    have he := congrArg (fun Y : M => α•Y) h
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hα,one_smul] at he
    unfold matrixKInverseVariableMap
    rw [smul_sub,smul_sub,← he]
    abel
  · intro h
    have he := congrArg (fun Y : M => α⁻¹•Y) h
    simp only [matrixKInverseVariableMap,smul_smul,inv_mul_cancel₀ hα,one_smul] at he
    rw [he]
    abel

/-- A positive native imaginary coercivity bound controls every genuine
inverse-variable resolvent by the reciprocal coercivity, including
nonnormal matrix parameters. This is the uniform compactness and
high-height contraction input for actual K solutions.
Source: Montanari--Saeed (2026), Appendix A, Lemmas 10--11.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_inverseVariable_resolvent_le_inv
    (X T : M) (hT : T.IsHermitian) (η : ℝ) (hη : 0<η)
    (hX : η•(1 : M)≤(imaginaryPart X : M)) :
    specNorm ((X-T)⁻¹)≤η⁻¹ := by
  have hXpos : (imaginaryPart X : M).PosDef :=
    ((Matrix.PosDef.one.smul hη).isStrictlyPositive.of_le hX).posDef
  have hu := inverseVariable_sub_isUnit X T hXpos hT
  have he : (X-T)*(-(X-T)⁻¹)= -1 := by
    rw [Matrix.mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  have hc : η•(1 : M)≤(imaginaryPart (X-T) : M) := by
    rwa [imaginaryPart_sub_hermitian X T hT]
  simpa only [specNorm_eq_norm,norm_neg] using
    Matrix.norm_le_inv_of_mul_eq_neg_one_of_imaginaryPart_ge hη he hc

private theorem imaginaryPart_hermitian_sandwich (T R : M) (hT : T.IsHermitian) :
    (imaginaryPart (T*R*T) : M)=T*(imaginaryPart R : M)*T := by
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul,hT.eq,Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  noncomm_ring

/-- The genuine inverse-variable map preserves the target imaginary
coercivity. This is proved for the actual nonlinear sample resolvents,
including singular and indefinite samples; no fixed-point positivity
conclusion is supplied as an assumption.
Source: Montanari--Saeed (2026), Appendix A, existence step in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem le_imaginaryPart_matrixKInverseVariableMap
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0≤α) (Z X : M) (hX : (imaginaryPart X : M).PosDef) :
    α•(imaginaryPart Z : M)≤(imaginaryPart (matrixKInverseVariableMap ν α Z X) : M) := by
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  have hL (Y : M) : L Y=(imaginaryPart Y : M) := rfl
  let f (T : selfAdjoint M) := T.val*(X-T.val)⁻¹*T.val
  have hiT : Integrable (fun T : selfAdjoint M => T.val) ν :=
    inverseVariable_integrable_continuous ν hν continuous_subtype_val
  have hif : Integrable f ν := inverseVariable_integrable_continuous ν hν
    ((continuous_subtype_val.mul (continuous_inverseVariable_resolvent X hX)).mul
      continuous_subtype_val)
  have hmean : L (∫ T : selfAdjoint M,T.val ∂ν)=0 := by
    rw [← L.integral_comp_comm hiT]
    have hz (T : selfAdjoint M) : L T.val=0 := by
      rw [hL]
      have hh : T.val.IsHermitian := T.property
      simp only [hh.isSelfAdjoint.imaginaryPart,ZeroMemClass.coe_zero]
    simp_rw [hz]
    exact integral_zero _ _
  have hnonpos (T : selfAdjoint M) : L (f T)≤0 := by
    have hA : (imaginaryPart (X-T.val) : M).PosDef := by
      rwa [imaginaryPart_sub_hermitian X T.val T.property]
    have hR := (posDef_imaginaryPart_neg_matrixInverse (X-T.val) hA).posSemidef
    have hT : T.val.IsHermitian := T.property
    have hsand : (-(imaginaryPart (f T) : M)).PosSemidef := by
      change (-(imaginaryPart (T.val*(X-T.val)⁻¹*T.val) : M)).PosSemidef
      rw [imaginaryPart_hermitian_sandwich T.val (X-T.val)⁻¹ hT]
      have he : (imaginaryPart (-(X-T.val)⁻¹) : M)=
          -(imaginaryPart ((X-T.val)⁻¹) : M) := by rw [map_neg]; rfl
      rw [he] at hR
      simpa only [hT.eq,Matrix.mul_neg,Matrix.neg_mul] using
        hR.mul_mul_conjTranspose_same T.val
    rw [hL]
    exact neg_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr hsand)
  have hI : L (∫ T,f T ∂ν)≤0 := by
    rw [← L.integral_comp_comm hif]
    exact integral_nonpos_of_ae (ae_of_all _ hnonpos)
  have he : (imaginaryPart (matrixKInverseVariableMap ν α Z X) : M)-
      α•(imaginaryPart Z : M)= -(α•L (∫ T,f T ∂ν)) := by
    change L (α•(Z-(∫ T : selfAdjoint M,T.val ∂ν)-(∫ T,f T ∂ν)))-α•L Z=_
    rw [map_smul,map_sub,map_sub,hmean,sub_zero]
    module
  apply sub_nonneg.mp
  rw [he]
  exact neg_nonneg.mpr (smul_nonpos_of_nonneg_of_nonpos hα hI)

end NLAlib

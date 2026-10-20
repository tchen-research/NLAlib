import NLAlib.Matrix.Functions.KTransformHalfPlane
import NLAlib.Matrix.Spectral.SpectralBounds

/-! # Dual Gram identities for the actual nonlinear K-transform

The opposite adjoint orientation of the exact imaginary-part identities
supplies the second row contraction needed for genuine upper-half-plane
uniqueness. Source: Montanari--Saeed (2026), Appendix A, Lemma 11.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem kDenominator_swap_unit (S T : M) (hS : IsUnit S)
    (hL : IsUnit (1+S*T)) : IsUnit (1+T*S) := by
  have he : 1+T*S=S⁻¹*(1+S*T)*S := by
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one]
    rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
    simp only [Matrix.one_mul]
  rw [he]
  exact ((Matrix.isUnit_nonsing_inv_iff.mpr hS).mul hL).mul hS

private theorem kResolvent_adjoint_upper (S T : M)
    (hS : (imaginaryPart S : M).PosDef) (hT : T.IsHermitian) :
    matrixKResolvent Sᴴ T=(matrixKResolvent S T)ᴴ := by
  have hL := isUnit_matrixKDenominator_of_posDef_imaginaryPart S T hS hT
  have hR := kDenominator_swap_unit S T (Matrix.isUnit_of_posDef_imaginaryPart hS) hL
  have hLa : IsUnit (1+Sᴴ*T) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hR.star
  have hRa : IsUnit (1+T*Sᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hL.star
  have ht : (1+T*Sᴴ)*T=T*(1+Sᴴ*T) := by noncomm_ring
  have he : (1+T*Sᴴ)*matrixKResolvent Sᴴ T=T := by
    unfold matrixKResolvent
    rw [← Matrix.mul_assoc,ht,Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hLa),Matrix.mul_one]
  calc
    _ = (1+T*Sᴴ)⁻¹*((1+T*Sᴴ)*matrixKResolvent Sᴴ T) := by
      rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hRa),
        Matrix.one_mul]
    _ = (1+T*Sᴴ)⁻¹*T := by rw [he]
    _ = _ := by
      simp only [matrixKResolvent,Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,
        Matrix.conjTranspose_add,Matrix.conjTranspose_one,hT.eq]

/-- The native K resolvent has the exact opposite-adjoint Gram identity
as well. This is derived from the actual two-resolvent formula and includes
singular or indefinite Hermitian samples.
Source: Montanari--Saeed (2026), Lemma 11, dual form of equation (163).
atlas: block-wishart-variational-edges (partial) -/
theorem imaginaryPart_matrixKResolvent_dual (S T : M)
    (hS : (imaginaryPart S : M).PosDef) (hT : T.IsHermitian) :
    (imaginaryPart (matrixKResolvent S T) : M) =
      -((matrixKResolvent S T)ᴴ*(imaginaryPart S : M)*matrixKResolvent S T) := by
  have hL := isUnit_matrixKDenominator_of_posDef_imaginaryPart S T hS hT
  have hR := kDenominator_swap_unit S T (Matrix.isUnit_of_posDef_imaginaryPart hS) hL
  have hLa : IsUnit (1+Sᴴ*T) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hR.star
  have ha := kResolvent_adjoint_upper S T hS hT
  have hd := matrixKResolvent_sub_matrixKResolvent Sᴴ S T hLa hL
  rw [ha,show Sᴴ-S=-(S-Sᴴ) by abel,Matrix.mul_neg,Matrix.neg_mul,neg_neg] at hd
  have he : matrixKResolvent S T-(matrixKResolvent S T)ᴴ =
      -((matrixKResolvent S T)ᴴ*(S-Sᴴ)*matrixKResolvent S T) := by
    calc
      _ = -((matrixKResolvent S T)ᴴ-matrixKResolvent S T) := by abel
      _ = _ := congrArg Neg.neg hd
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose]
  rw [he]
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_neg]

/-- The genuine K resolvent satisfies the source uniform norm bound
without requiring an invertible Hermitian sample. The dual Gram identity
gives the estimate directly, so no perturbation of singular samples is
assumed. Source: Montanari--Saeed (2026), Lemma 11, equation (163).
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_matrixKResolvent_le_inv_imaginaryPart (S T : M)
    (hS : (imaginaryPart S : M).PosDef) (hT : T.IsHermitian) :
    specNorm (matrixKResolvent S T)≤specNorm ((imaginaryPart S : M)⁻¹) := by
  let B : M := imaginaryPart S
  let R := cfc (fun x => (Real.sqrt x)⁻¹) B
  let Q := cfc Real.sqrt B
  let U := matrixKResolvent S T
  have hR : R.IsHermitian := cfc_predicate _ _
  have hQ : Q.IsHermitian := cfc_predicate _ _
  have hRn : specNorm R^2=specNorm B⁻¹ := by
    rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self,hR.eq,
      ← inv_eq_cfc_inv_sqrt_mul_self hS]
  have hgram : (Q*U)ᴴ*(Q*U)=-(imaginaryPart U : M) := by
    rw [Matrix.conjTranspose_mul,hQ.eq,Matrix.mul_assoc,
      ← Matrix.mul_assoc Q Q,cfc_sqrt_mul_self hS]
    have hh := imaginaryPart_matrixKResolvent_dual S T hS hT
    change (imaginaryPart U : M)=-(Uᴴ*B*U) at hh
    rw [hh,neg_neg]
    simp only [B,Matrix.mul_assoc]
  have hQU : specNorm (Q*U)^2≤specNorm U := by
    rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self,hgram,specNorm_neg]
    simpa only [specNorm_eq_norm, ← AddSubgroup.norm_coe] using imaginaryPart.norm_le U
  have hU : specNorm U≤specNorm R*specNorm (Q*U) := by
    calc
      _ = specNorm (R*(Q*U)) := by
        rw [← Matrix.mul_assoc,cfc_inv_sqrt_mul_sqrt hS,Matrix.one_mul]
      _ ≤ _ := specNorm_mul_le _ _
  have hsquare : specNorm U^2≤specNorm B⁻¹*specNorm U := by
    calc
      _ ≤ (specNorm R*specNorm (Q*U))^2 :=
        pow_le_pow_left₀ (specNorm_nonneg U) hU 2
      _ = specNorm B⁻¹*specNorm (Q*U)^2 := by rw [mul_pow,hRn]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQU (specNorm_nonneg B⁻¹)
  change specNorm U≤specNorm B⁻¹
  by_cases hz : specNorm U=0
  · simpa only [hz] using specNorm_nonneg B⁻¹
  · have hpos : 0<specNorm U := (specNorm_nonneg U).lt_of_ne (Ne.symm hz)
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [pow_two,mul_comm] using hsquare)

private theorem imaginaryPart_inv_dual (S : M) (hS : IsUnit S) :
    (imaginaryPart S⁻¹ : M) = -(S⁻¹ᴴ*(imaginaryPart S : M)*S⁻¹) := by
  have hleft : S⁻¹ᴴ*Sᴴ=1 := by
    rw [← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),Matrix.conjTranspose_one]
  have hd : S⁻¹ᴴ*(S-Sᴴ)*S⁻¹=S⁻¹ᴴ-S⁻¹ := by
    calc
      _ = S⁻¹ᴴ*(S*S⁻¹)-(S⁻¹ᴴ*Sᴴ)*S⁻¹ := by
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),hleft]
        simp only [Matrix.mul_one,Matrix.one_mul]
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,Matrix.mul_smul,Matrix.smul_mul]
  rw [hd]
  module

/-- The actual compact-support K transform satisfies its dual imaginary
Gram identity. This is the second native positivity identity used in the
upper-half-plane uniqueness proof, not a linear Dyson substitution.
Source: Montanari--Saeed (2026), Lemma 11, dual form of equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem imaginaryPart_matrixKTransform_dual
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (S : M) (hS : (imaginaryPart S : M).PosDef) :
    (imaginaryPart (matrixKTransform ν α S) : M) =
      α⁻¹ • (S⁻¹ᴴ*(imaginaryPart S : M)*S⁻¹) -
        ∫ T, (matrixKResolvent S T.val)ᴴ*(imaginaryPart S : M)*matrixKResolvent S T.val ∂ν := by
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  have hL (A : M) : L A=(imaginaryPart A : M) := rfl
  have hi := integrable_matrixKResolvent_of_mem_domain ν hν
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hS)
  have he : L (∫ T, matrixKResolvent S T.val ∂ν) =
      -(∫ T, (matrixKResolvent S T.val)ᴴ*(imaginaryPart S : M)*matrixKResolvent S T.val ∂ν) := by
    have heT (T : selfAdjoint M) : L (matrixKResolvent S T.val) =
        -((matrixKResolvent S T.val)ᴴ*(imaginaryPart S : M)*matrixKResolvent S T.val) := by
      rw [hL]
      exact imaginaryPart_matrixKResolvent_dual S T.val hS T.property
    rw [← L.integral_comp_comm hi]
    simp_rw [heT]
    rw [integral_neg]
  change L ((∫ T, matrixKResolvent S T.val ∂ν)-α⁻¹•S⁻¹)=_
  rw [map_sub,map_smul,he,hL,imaginaryPart_inv_dual S (Matrix.isUnit_of_posDef_imaginaryPart hS),
    smul_neg]
  abel

end NLAlib

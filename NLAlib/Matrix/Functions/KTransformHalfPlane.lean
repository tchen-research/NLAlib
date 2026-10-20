import NLAlib.Matrix.Functions.KTransformDifference
import NLAlib.ForMathlib.Analysis.Matrix.ImaginaryInvertibility
import NLAlib.ForMathlib.Analysis.Matrix.ImaginaryCoercivity
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Actual K-transform identities on the matrix upper half-plane

Positive native imaginary parts imply all genuine support denominators
are invertible. The exact imaginary-part identities are proved for the
nonlinear rational transform itself. Source: Montanari--Saeed (2026),
Appendix A, Lemmas 10--11, equation (164).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem imaginaryPart_matrix_inv (S : Matrix n n ℂ) (hS : IsUnit S) :
    (imaginaryPart S⁻¹ : Matrix n n ℂ) =
      -(S⁻¹*(imaginaryPart S : Matrix n n ℂ)*S⁻¹ᴴ) := by
  have hstar : IsUnit Sᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hS.star
  have hdiff : S⁻¹*(S-Sᴴ)*S⁻¹ᴴ=S⁻¹ᴴ-S⁻¹ := by
    rw [Matrix.mul_sub,Matrix.sub_mul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),Matrix.one_mul]
    rw [Matrix.mul_assoc,Matrix.conjTranspose_nonsing_inv,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hstar),Matrix.mul_one]
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,
    Matrix.mul_smul,Matrix.smul_mul]
  rw [hdiff]
  module

private theorem neg_imaginaryPart_matrix_inv_posDef
    {S : Matrix n n ℂ} (hS : (imaginaryPart S : Matrix n n ℂ).PosDef) :
    (-(imaginaryPart S⁻¹ : Matrix n n ℂ)).PosDef := by
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hS
  rw [imaginaryPart_matrix_inv S hu,neg_neg]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (Matrix.isUnit_nonsing_inv_iff.mpr hu)).mpr hS

/-- A positive-imaginary matrix makes the actual rational K denominator
invertible for every Hermitian sample, including singular or indefinite
samples. This is the native source upper-half-plane domain bridge.
Source: Montanari--Saeed (2026), Lemma 10.
atlas: block-wishart-variational-edges (partial) -/
theorem isUnit_matrixKDenominator_of_posDef_imaginaryPart
    (S T : Matrix n n ℂ) (hS : (imaginaryPart S : Matrix n n ℂ).PosDef)
    (hT : T.IsHermitian) : IsUnit (1+S*T) := by
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hS
  have him : (imaginaryPart (-(S⁻¹+T)) : Matrix n n ℂ) =
      -(imaginaryPart S⁻¹ : Matrix n n ℂ) := by
    rw [map_neg,map_add,hT.isSelfAdjoint.imaginaryPart,add_zero]
    rfl
  have hA : IsUnit (S⁻¹+T) := by
    have hp : (imaginaryPart (-(S⁻¹+T)) : Matrix n n ℂ).PosDef := by
      rw [him]
      exact neg_imaginaryPart_matrix_inv_posDef hS
    simpa only [neg_neg] using (Matrix.isUnit_of_posDef_imaginaryPart hp).neg
  have he : 1+S*T=S*(S⁻¹+T) := by
    rw [Matrix.mul_add,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  rw [he]
  exact hu.mul hA

private theorem matrixKResolvent_pushThrough
    (S T : Matrix n n ℂ) (hS : IsUnit (1+S*T)) (hT : IsUnit (1+T*S)) :
    matrixKResolvent S T=(1+T*S)⁻¹*T := by
  have ht : (1+T*S)*T=T*(1+S*T) := by noncomm_ring
  have hmul : (1+T*S)*matrixKResolvent S T=T := by
    unfold matrixKResolvent
    rw [← Matrix.mul_assoc,ht,Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),Matrix.mul_one]
  calc
    _ = ((1+T*S)⁻¹*(1+T*S))*matrixKResolvent S T := by
      rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hT),Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc,hmul]

private theorem matrixKResolvent_adjoint
    (S T : Matrix n n ℂ) (hT : T.IsHermitian)
    (hL : IsUnit (1+S*T)) (hR : IsUnit (1+T*S)) :
    matrixKResolvent Sᴴ T=(matrixKResolvent S T)ᴴ := by
  have hLa : IsUnit (1+Sᴴ*T) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hR.star
  have hRa : IsUnit (1+T*Sᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hL.star
  rw [matrixKResolvent_pushThrough Sᴴ T hLa hRa]
  simp only [matrixKResolvent,Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_add,Matrix.conjTranspose_one,hT.eq]

/-- The actual K resolvent has its exact negative Gram imaginary part.
Every inverse is justified by the original positive imaginary matrix;
the Hermitian sample may be singular or indefinite.
Source: Montanari--Saeed (2026), Lemma 11, equation (163).
atlas: block-wishart-variational-edges (partial) -/
theorem imaginaryPart_matrixKResolvent
    (S T : Matrix n n ℂ) (hS : (imaginaryPart S : Matrix n n ℂ).PosDef)
    (hT : T.IsHermitian) :
    (imaginaryPart (matrixKResolvent S T) : Matrix n n ℂ) =
      -(matrixKResolvent S T*(imaginaryPart S : Matrix n n ℂ)*(matrixKResolvent S T)ᴴ) := by
  have hL := isUnit_matrixKDenominator_of_posDef_imaginaryPart S T hS hT
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hS
  have hR : IsUnit (1+T*S) := by
    have he : 1+T*S=S⁻¹*(1+S*T)*S := by
      simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one]
      rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
      simp only [Matrix.one_mul]
    rw [he]
    exact ((Matrix.isUnit_nonsing_inv_iff.mpr hu).mul hL).mul hu
  have hLa : IsUnit (1+Sᴴ*T) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hR.star
  have ha := matrixKResolvent_adjoint S T hT hL hR
  have hd := matrixKResolvent_sub_matrixKResolvent S Sᴴ T hL hLa
  rw [ha] at hd
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose]
  rw [hd]
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_neg]

/-- Positive native imaginary parts imply membership in the genuine
simultaneous K-transform inverse domain for any Hermitian measure law. -/
theorem mem_matrixKTransformDomain_of_posDef_imaginaryPart
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) {S : Matrix n n ℂ}
    (hS : (imaginaryPart S : Matrix n n ℂ).PosDef) : S∈matrixKTransformDomain ν :=
  ⟨Matrix.isUnit_of_posDef_imaginaryPart hS,fun T _ =>
    isUnit_matrixKDenominator_of_posDef_imaginaryPart S T.val hS T.property⟩

/-- The nonlinear rational K-transform itself satisfies the exact source
imaginary-part identity. The actual law is finite and compactly supported;
all genuine inverses and Bochner integrability are derived.
Source: Montanari--Saeed (2026), Lemma 11, equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem imaginaryPart_matrixKTransform
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : (imaginaryPart S : Matrix n n ℂ).PosDef) :
    (imaginaryPart (matrixKTransform ν α S) : Matrix n n ℂ) =
      α⁻¹ • (S⁻¹*(imaginaryPart S : Matrix n n ℂ)*S⁻¹ᴴ) -
        ∫ T, matrixKResolvent S T.val*(imaginaryPart S : Matrix n n ℂ)*
          (matrixKResolvent S T.val)ᴴ ∂ν := by
  let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
    (((selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtype).comp imaginaryPart).toContinuousLinearMap
  have hL (A : Matrix n n ℂ) : L A=(imaginaryPart A : Matrix n n ℂ) := rfl
  have hi := integrable_matrixKResolvent_of_mem_domain ν hν
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hS)
  have he : L (∫ T, matrixKResolvent S T.val ∂ν) =
      -(∫ T, matrixKResolvent S T.val*(imaginaryPart S : Matrix n n ℂ)*
        (matrixKResolvent S T.val)ᴴ ∂ν) := by
    have heT (T : selfAdjoint (Matrix n n ℂ)) : L (matrixKResolvent S T.val) =
        -(matrixKResolvent S T.val*(imaginaryPart S : Matrix n n ℂ)*
          (matrixKResolvent S T.val)ᴴ) := by
      rw [hL]
      exact imaginaryPart_matrixKResolvent S T.val hS T.property
    rw [← L.integral_comp_comm hi]
    simp_rw [heT]
    rw [integral_neg]
  change L ((∫ T, matrixKResolvent S T.val ∂ν)-α⁻¹•S⁻¹)=_
  rw [map_sub,map_smul,he,hL,imaginaryPart_matrix_inv S (Matrix.isUnit_of_posDef_imaginaryPart hS),smul_neg]
  abel

end NLAlib

import NLAlib.Matrix.Functions.KTransformExteriorNorm
import NLAlib.Matrix.Functions.KTransformInverseImaginary

/-! # Exterior imaginary bounds for the actual nonlinear K branch

The true inverse-variable imaginary equation is contractive outside the
derived sample interval. It gives the height bound required by the
Stieltjes support theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem exteriorImaginary_scalar_im (z : ℂ) :
    (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
  have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
  simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]

/-- Outside the native sample-dependent interval, the actual analytic K
branch has imaginary part bounded by its height. Both the exterior norm
selection and imaginary contraction follow from the original nonlinear
equation; no support or boundary-value premise is supplied.
Source: Montanari--Saeed (2026), Lemma 1, compact-support argument.
atlas: block-wishart-variational-edges (partial) -/
theorem norm_imaginaryPart_matrixKTransform_solution_le_exterior
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α R : ℝ) (hα : 0<α) (hR : 0<R) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (z : ℂ) (hz : 0<z.im) (hfar : 4*(α+1)*R<α*|z.re|) :
    ‖(imaginaryPart (α•F z) : M)‖≤
      (2*α^2*(((α+1)*R)⁻¹)^2)*z.im := by
  let X := -(F z)⁻¹
  let q := ((α+1)*R)⁻¹
  have hq : 0≤q := by dsimp only [q]; positivity
  have hX : (imaginaryPart X : M).PosDef :=
    posDef_imaginaryPart_neg_matrixInverse (F z) (hF z hz).1
  have hnorm := norm_inverseVariable_resolvents_matrixKTransform_solution_le_exterior
    ν hν α R hα hR F hFa hF hbound z hz hfar
  have hN := norm_imaginaryPart_matrixKInverseVariableMap_le ν hν α hα.le
    (z•1) X hX R q hR.le hq hbound hnorm.2
  have hfixed := (matrixKTransform_solution_inverse_variable ν hν α hα
    (z•1) (F z) (hF z hz).1 (hF z hz).2).1
  rw [← hfixed] at hN
  have hscalar : ‖(imaginaryPart (z•(1 : M)) : M)‖≤z.im := by
    rw [exteriorImaginary_scalar_im,norm_smul,Real.norm_of_nonneg hz.le]
    simpa only [mul_one,specNorm_eq_norm] using
      mul_le_mul_of_nonneg_left (specNorm_one_le (n := n) (𝕜 := ℂ)) hz.le
  have hRq : R*q=(α+1)⁻¹ := by
    dsimp only [q]
    field_simp [hR.ne',(by linarith : α+1≠0)]
  have hc : α*(R^2*q^2)≤1/2 := by
    rw [← mul_pow,hRq,inv_pow,← div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<α+1))).mpr
    nlinarith [sq_nonneg α]
  have hNB : ‖(imaginaryPart X : M)‖≤α*z.im+(1/2)*‖(imaginaryPart X : M)‖ := by
    calc
      _ ≤ α*‖(imaginaryPart (z•(1 : M)) : M)‖+
          α*(R^2*q^2*‖(imaginaryPart X : M)‖) := hN
      _ ≤ α*z.im+(α*(R^2*q^2))*‖(imaginaryPart X : M)‖ := by
        rw [mul_assoc α]
        exact add_le_add (mul_le_mul_of_nonneg_left hscalar hα.le) le_rfl
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hB : ‖(imaginaryPart X : M)‖≤2*α*z.im := by linarith
  have hunit := Matrix.isUnit_of_posDef_imaginaryPart (hF z hz).1
  have he : X*F z= -1 := by
    dsimp only [X]
    rw [Matrix.neg_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]
  have hIm := Matrix.imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one he
  have hstar : ‖(F z)ᴴ‖≤q := by
    simpa only [← Matrix.star_eq_conjTranspose,norm_star] using hnorm.1
  have hSF : ‖(imaginaryPart (F z) : M)‖≤q^2*(2*α*z.im) := by
    rw [hIm]
    calc
      _ ≤ ‖(F z)ᴴ*(imaginaryPart X : M)‖*‖F z‖ := norm_mul_le _ _
      _ ≤ ‖(F z)ᴴ‖*‖(imaginaryPart X : M)‖*‖F z‖ := by
        gcongr; exact norm_mul_le _ _
      _ ≤ q*(2*α*z.im)*q := by gcongr; exact hnorm.1
      _ = _ := by ring
  have hscale : (imaginaryPart (α•F z) : M)=α•(imaginaryPart (F z) : M) := by
    rw [map_smul]; rfl
  rw [hscale,norm_smul,Real.norm_of_nonneg hα.le]
  calc
    _ ≤ α*(q^2*(2*α*z.im)) := mul_le_mul_of_nonneg_left hSF hα.le
    _ = _ := by ring

end NLAlib

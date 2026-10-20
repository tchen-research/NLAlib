import NLAlib.Matrix.Functions.KTransformInverseVariable

/-! # Native coercive bounds on actual upper-half-plane K solutions

Negative inversion of an actual solution satisfies the genuine
inverse-variable equation and inherits the target imaginary coercivity.
Compact sample bounds then control both the solution and its inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem inverseBounds_neg_inverse_involutive (S : M) (hS : IsUnit S) :
    -(-S⁻¹)⁻¹=S := by
  have hi : (-S⁻¹)⁻¹= -S := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.neg_mul,Matrix.mul_neg,neg_neg,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
  rw [hi,neg_neg]

/-- An actual upper-half-plane K solution yields the actual inverse
fixed point and its target imaginary coercivity. These conclusions
follow from the original equation, rather than serving as premises.
Source: Montanari--Saeed (2026), Appendix A, equation (164).
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_solution_inverse_variable
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z S : M) (hS : (imaginaryPart S : M).PosDef)
    (hK : matrixKTransform ν α S=Z) :
    -S⁻¹=matrixKInverseVariableMap ν α Z (-S⁻¹) ∧
      α•(imaginaryPart Z : M)≤(imaginaryPart (-S⁻¹) : M) := by
  have hX := posDef_imaginaryPart_neg_matrixInverse S hS
  have hinvol := inverseBounds_neg_inverse_involutive S
    (Matrix.isUnit_of_posDef_imaginaryPart hS)
  have hKX : matrixKTransform ν α (-(-S⁻¹)⁻¹)=Z := by rwa [hinvol]
  have hfixed := (matrixKTransform_neg_inverse_eq_iff_fixedPoint ν hν α hα.ne' Z (-S⁻¹) hX).mp hKX
  refine ⟨hfixed,?_⟩
  have hi := le_imaginaryPart_matrixKInverseVariableMap ν hν α hα.le Z (-S⁻¹) hX
  rwa [← hfixed] at hi

/-- The genuine inverse-variable map is bounded uniformly on a fixed
coercive half-space by the actual compact Hermitian sample bound.
Source: Montanari--Saeed (2026), Appendix A, compactness step in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_matrixKInverseVariableMap_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν]
    (α : ℝ) (hα : 0≤α) (Z X : M) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hX : η•(1 : M)≤(imaginaryPart X : M)) :
    specNorm (matrixKInverseVariableMap ν α Z X)≤α*(specNorm Z+R+R^2*η⁻¹) := by
  have hET : ‖∫ T : selfAdjoint M,T.val ∂ν‖≤R := by
    have hpt : ∀ᵐ T : selfAdjoint M ∂ν, ‖T.val‖≤R := by
      filter_upwards [ν.support_mem_ae] with T hT
      simpa only [specNorm_eq_norm] using hbound T hT
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := ν) hpt
  have hER : ‖∫ T : selfAdjoint M,T.val*(X-T.val)⁻¹*T.val ∂ν‖≤R^2*η⁻¹ := by
    have hpt : ∀ᵐ T : selfAdjoint M ∂ν, ‖T.val*(X-T.val)⁻¹*T.val‖≤R^2*η⁻¹ := by
      filter_upwards [ν.support_mem_ae] with T hT
      have hTN : ‖T.val‖≤R := by simpa only [specNorm_eq_norm] using hbound T hT
      have hRN : ‖(X-T.val)⁻¹‖≤η⁻¹ := by
        simpa only [specNorm_eq_norm] using
          specNorm_inverseVariable_resolvent_le_inv X T.val T.property η hη hX
      have hR0 : 0≤R := (norm_nonneg T.val).trans hTN
      calc
        _ ≤ ‖T.val‖*‖(X-T.val)⁻¹‖*‖T.val‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ R*η⁻¹*R := by gcongr
        _ = _ := by ring
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := ν) hpt
  have htriangle : ‖Z-(∫ T : selfAdjoint M,T.val ∂ν)-
      (∫ T : selfAdjoint M,T.val*(X-T.val)⁻¹*T.val ∂ν)‖≤‖Z‖+R+R^2*η⁻¹ := by
    calc
      _ ≤ ‖Z-(∫ T : selfAdjoint M,T.val ∂ν)‖+
          ‖∫ T : selfAdjoint M,T.val*(X-T.val)⁻¹*T.val ∂ν‖ := norm_sub_le _ _
      _ ≤ (‖Z‖+‖∫ T : selfAdjoint M,T.val ∂ν‖)+
          ‖∫ T : selfAdjoint M,T.val*(X-T.val)⁻¹*T.val ∂ν‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by gcongr
  unfold matrixKInverseVariableMap
  simpa only [specNorm_eq_norm,norm_smul,Real.norm_of_nonneg hα] using
    mul_le_mul_of_nonneg_left htriangle hα

/-- Actual upper-half-plane K solutions have a uniform inverse bound
on every coercive target region. This is the native finite-dimensional
compactness estimate needed to continue high-height existence.
Source: Montanari--Saeed (2026), Appendix A, Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_inverse_of_matrixKTransform_solution_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z S : M) (hS : (imaginaryPart S : M).PosDef)
    (hK : matrixKTransform ν α S=Z) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hZ : η•(1 : M)≤α•(imaginaryPart Z : M)) :
    specNorm S⁻¹≤α*(specNorm Z+R+R^2*η⁻¹) := by
  obtain ⟨hfixed,hcoercive⟩ := matrixKTransform_solution_inverse_variable ν hν α hα Z S hS hK
  have hn := specNorm_matrixKInverseVariableMap_le ν α hα.le Z (-S⁻¹) η R hη hbound
    (hZ.trans hcoercive)
  rwa [← hfixed,specNorm_neg] at hn

/-- The actual upper-half-plane K solution has the reciprocal target
coercivity bound, derived from its native inverse equation. In
particular, scalar targets give `1/(α Im z)` without a branch assumption.
Source: Montanari--Saeed (2026), Appendix A, Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_of_matrixKTransform_solution_le_inv
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z S : M) (hS : (imaginaryPart S : M).PosDef)
    (hK : matrixKTransform ν α S=Z) (η : ℝ) (hη : 0<η)
    (hZ : η•(1 : M)≤α•(imaginaryPart Z : M)) :
    specNorm S≤η⁻¹ := by
  have hcoercive := (matrixKTransform_solution_inverse_variable ν hν α hα Z S hS hK).2
  have hu := Matrix.isUnit_of_posDef_imaginaryPart hS
  have he : (-S⁻¹)*S= -1 := by
    rw [Matrix.neg_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  simpa only [specNorm_eq_norm] using
    Matrix.norm_le_inv_of_mul_eq_neg_one_of_imaginaryPart_ge hη he (hZ.trans hcoercive)

end NLAlib

import NLAlib.Matrix.Functions.KTransformInverseVariable
import Mathlib.Topology.MetricSpace.Contracting

/-! # Actual high-imaginary K solutions by Banach contraction

The genuine inverse-variable map contracts a closed positive-imaginary
half-space at sufficiently large height. Bounds come from the actual
Hermitian sample support and ordinary nonnormal inverse coercivity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter Function
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology NNReal
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem inverseContraction_posDef (X : M) (η : ℝ) (hη : 0<η)
    (hX : η•(1 : M)≤(imaginaryPart X : M)) : (imaginaryPart X : M).PosDef :=
  ((Matrix.PosDef.one.smul hη).isStrictlyPositive.of_le hX).posDef

private theorem inverseContraction_sub_isUnit (X T : M) (hT : T.IsHermitian)
    (η : ℝ) (hη : 0<η) (hX : η•(1 : M)≤(imaginaryPart X : M)) : IsUnit (X-T) := by
  apply Matrix.isUnit_of_posDef_imaginaryPart
  rw [map_sub,hT.isSelfAdjoint.imaginaryPart,sub_zero]
  exact inverseContraction_posDef X η hη hX

private theorem inverseContraction_kernel_integrable
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (X : M) (hX : (imaginaryPart X : M).PosDef) :
    Integrable (fun T : selfAdjoint M => T.val*(X-T.val)⁻¹*T.val) ν := by
  have hiT : Integrable (fun T : selfAdjoint M => T.val) ν := by
    have hi := continuous_subtype_val.continuousOn.integrableOn_compact (μ := ν) hν
    have hre : ν.restrict ν.support=ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
    rwa [IntegrableOn,hre] at hi
  have hiη := integrable_matrixKResolvent_of_mem_domain ν hν
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν
      (posDef_imaginaryPart_neg_matrixInverse X hX))
  apply (hiη.sub hiT).congr
  exact ae_of_all _ fun T => by
    change matrixKResolvent (-X⁻¹) T.val-T.val=T.val*(X-T.val)⁻¹*T.val
    rw [matrixKResolvent_neg_inverse_eq X T.val hX T.property]
    abel

/-- The actual sample resolvent sandwich has the true inverse-variable
Lipschitz bound on a coercive matrix half-space. No normality is required
of the two spectral matrix parameters.
Source: Montanari--Saeed (2026), Appendix A, high-height existence in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_inverseVariable_kernel_sub_le
    (X Y T : M) (hT : T.IsHermitian) (η : ℝ) (hη : 0<η)
    (hX : η•(1 : M)≤(imaginaryPart X : M))
    (hY : η•(1 : M)≤(imaginaryPart Y : M)) :
    specNorm (T*(X-T)⁻¹*T-T*(Y-T)⁻¹*T)≤
      specNorm T^2*(η⁻¹)^2*specNorm (X-Y) := by
  have hXu := inverseContraction_sub_isUnit X T hT η hη hX
  have hYu := inverseContraction_sub_isUnit Y T hT η hη hY
  have hd : (X-T)⁻¹-(Y-T)⁻¹=(X-T)⁻¹*(Y-X)*(Y-T)⁻¹ := by
    rw [Matrix.inv_sub_inv ⟨fun _ => hYu,fun _ => hXu⟩]
    congr 2
    abel
  have hXR := specNorm_inverseVariable_resolvent_le_inv X T hT η hη hX
  have hYR := specNorm_inverseVariable_resolvent_le_inv Y T hT η hη hY
  have hleft : specNorm (T*(X-T)⁻¹)≤specNorm T*η⁻¹ :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hXR (specNorm_nonneg T))
  have hright : specNorm ((Y-T)⁻¹*T)≤η⁻¹*specNorm T :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hYR (specNorm_nonneg T))
  have hdiff : T*(X-T)⁻¹*T-T*(Y-T)⁻¹*T=
      (T*(X-T)⁻¹)*(Y-X)*((Y-T)⁻¹*T) := by
    rw [← Matrix.sub_mul,← Matrix.mul_sub,hd]
    simp only [Matrix.mul_assoc]
  calc
    _ = specNorm ((T*(X-T)⁻¹)*(Y-X)*((Y-T)⁻¹*T)) := by rw [hdiff]
    _ ≤ specNorm (T*(X-T)⁻¹)*specNorm (Y-X)*specNorm ((Y-T)⁻¹*T) :=
      (specNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ (specNorm T*η⁻¹)*specNorm (Y-X)*(η⁻¹*specNorm T) := by
      have hNT := specNorm_nonneg T
      have hNXY := specNorm_nonneg (Y-X)
      have hNYT := specNorm_nonneg ((Y-T)⁻¹*T)
      gcongr
    _ = _ := by rw [specNorm_sub_comm Y X]; ring

/-- The true nonlinear inverse-variable map has a uniform contraction
constant derived from the actual compact sample law and coercivity.
Source: Montanari--Saeed (2026), Appendix A, high-height existence in Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_matrixKInverseVariableMap_sub_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0≤α) (Z X Y : M) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hX : η•(1 : M)≤(imaginaryPart X : M))
    (hY : η•(1 : M)≤(imaginaryPart Y : M)) :
    specNorm (matrixKInverseVariableMap ν α Z X-matrixKInverseVariableMap ν α Z Y)≤
      (α*R^2*(η⁻¹)^2)*specNorm (X-Y) := by
  let f (X : M) (T : selfAdjoint M) := T.val*(X-T.val)⁻¹*T.val
  have hiX : Integrable (f X) ν := inverseContraction_kernel_integrable ν hν X
    (inverseContraction_posDef X η hη hX)
  have hiY : Integrable (f Y) ν := inverseContraction_kernel_integrable ν hν Y
    (inverseContraction_posDef Y η hη hY)
  have he : matrixKInverseVariableMap ν α Z X-matrixKInverseVariableMap ν α Z Y=
      -(α•∫ T,f X T-f Y T ∂ν) := by
    rw [integral_sub hiX hiY]
    unfold matrixKInverseVariableMap
    module
  have hI : specNorm (∫ T,f X T-f Y T ∂ν)≤R^2*(η⁻¹)^2*specNorm (X-Y) := by
    have hpt : ∀ᵐ T ∂ν, ‖f X T-f Y T‖≤R^2*(η⁻¹)^2*specNorm (X-Y) := by
      filter_upwards [ν.support_mem_ae] with T hT
      rw [← specNorm_eq_norm]
      exact (specNorm_inverseVariable_kernel_sub_le X Y T.val T.property η hη hX hY).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (specNorm_nonneg T.val) (hbound T hT) 2) (sq_nonneg η⁻¹))
          (specNorm_nonneg (X-Y)))
    simpa only [specNorm_eq_norm,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := ν) hpt
  calc
    _ = α*specNorm (∫ T,f X T-f Y T ∂ν) := by
      rw [he,specNorm_eq_norm,norm_neg,norm_smul,Real.norm_of_nonneg hα,specNorm_eq_norm]
    _ ≤ α*(R^2*(η⁻¹)^2*specNorm (X-Y)) := mul_le_mul_of_nonneg_left hI hα
    _ = _ := by ring

/-- A genuine upper-half-plane K solution exists whenever the actual
inverse-variable map is at high enough imaginary height to contract.
The closed domain, its nonemptiness, map preservation, and Banach
contraction all follow from native matrix and sample-law hypotheses.
Source: Montanari--Saeed (2026), Appendix A, high-height part of Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_matrixKTransform_solution_of_imaginary_coercive_contraction
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Z : M) (η R : ℝ) (hη : 0<η)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hZ : η•(1 : M)≤α•(imaginaryPart Z : M))
    (hsmall : α*R^2*(η⁻¹)^2<1) :
    ∃ S : M, (imaginaryPart S : M).PosDef ∧ matrixKTransform ν α S=Z ∧
      specNorm S≤η⁻¹ := by
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  let U : Set M := {X | η•(1 : M)≤(imaginaryPart X : M)}
  let Φ : M → M := matrixKInverseVariableMap ν α Z
  have hUc : IsClosed U := isClosed_Ici.preimage L.continuous
  have hmap : MapsTo Φ U U := by
    intro X hX
    exact hZ.trans (le_imaginaryPart_matrixKInverseVariableMap ν hν α hα.le Z X
      (inverseContraction_posDef X η hη hX))
  let K : ℝ≥0 := ⟨α*R^2*(η⁻¹)^2,by positivity⟩
  have hKcoe : (K : ℝ)=α*R^2*(η⁻¹)^2 := rfl
  have hcontract : ContractingWith K (hmap.restrict Φ U U) := by
    refine ⟨?_,LipschitzWith.of_dist_le_mul fun X Y => ?_⟩
    · exact hsmall
    · change dist (Φ X.val) (Φ Y.val)≤(K : ℝ)*dist X.val Y.val
      rw [hKcoe]
      simpa only [dist_eq_norm,specNorm_eq_norm,Φ] using
        specNorm_matrixKInverseVariableMap_sub_le ν hν α hα.le Z X.val Y.val
          η R hη hbound X.property Y.property
  let X0 : M := ((η : ℂ)*Complex.I)•1
  have hX0 : X0∈U := by
    have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
    change η•(1 : M)≤(imaginaryPart (((η : ℂ)*Complex.I)•(1 : M)) : M)
    simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]
  obtain ⟨X,hX,hfix,_,_⟩ := ContractingWith.exists_fixedPoint' hUc.isComplete hmap hcontract hX0
    (edist_ne_top X0 (Φ X0))
  have hXpos := inverseContraction_posDef X η hη hX
  refine ⟨-X⁻¹,posDef_imaginaryPart_neg_matrixInverse X hXpos,?_,?_⟩
  · exact (matrixKTransform_neg_inverse_eq_iff_fixedPoint ν hν α hα.ne' Z X hXpos).mpr hfix.eq.symm
  · have hu := Matrix.isUnit_of_posDef_imaginaryPart hXpos
    have he : X*(-X⁻¹)= -1 := by
      rw [Matrix.mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
    simpa only [specNorm_eq_norm] using
      Matrix.norm_le_inv_of_mul_eq_neg_one_of_imaginaryPart_ge hη he hX

end NLAlib

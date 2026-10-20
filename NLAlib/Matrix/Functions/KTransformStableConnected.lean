import NLAlib.Matrix.Functions.KTransformStableRays

/-!
# Connectedness of the actual inverse-variable stable K-domain

The genuine certificate rays enter a common convex region of sufficiently
large positive matrices. Compact support constructs that region and its
actual integral certificate. Source: Montanari--Saeed (2026), Lemma 9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private theorem posDef_of_posDef_le_complex {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hAB : A ≤ B) : B.PosDef := by
  have hp := hA.add_posSemidef (Matrix.le_iff.mp hAB)
  convert! hp using 1; abel

private theorem inv_real_smul_one {c : ℝ} (hc : c≠0) :
    (c•(1 : Matrix n n ℂ))⁻¹ = c⁻¹•1 := by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,inv_mul_cancel₀ hc,one_smul]

private theorem norm_inv_le_of_scalar_gap {A : Matrix n n ℂ} {c : ℝ}
    (hc : 0<c) (hgap : c•(1 : Matrix n n ℂ) ≤ A) : ‖A⁻¹‖ ≤ c⁻¹ := by
  have hI : (c•(1 : Matrix n n ℂ)).PosDef := Matrix.PosDef.one.smul hc
  have hA := posDef_of_posDef_le_complex hI hgap
  have hle : A⁻¹ ≤ c⁻¹•(1 : Matrix n n ℂ) := by
    have hh := CStarAlgebra.ringInverse_le_ringInverse hgap hI.isStrictlyPositive
    simpa only [← Matrix.nonsing_inv_eq_ringInverse,inv_real_smul_one hc.ne'] using hh
  apply (CStarAlgebra.norm_le_iff_le_algebraMap A⁻¹ (inv_pos.mpr hc).le
    hA.inv.posSemidef.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using hle

private theorem posDef_one_sub_of_isHermitian_norm_lt_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hAn : ‖A‖<1) : (1-A).PosDef := by
  have hle : A ≤ ‖A‖•(1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hA.isSelfAdjoint.le_algebraMap_norm_self
  have hp := (Matrix.PosDef.one.smul (sub_pos.mpr hAn)).add_posSemidef
    (Matrix.le_iff.mp hle)
  convert! hp using 1; module

private theorem scalar_lower_bound_of_posDef (B : Matrix n n ℂ) (hB : B.PosDef) :
    (‖B⁻¹‖+1)⁻¹ • (1 : Matrix n n ℂ) ≤ B := by
  have hb : 0<‖B⁻¹‖+1 := by positivity
  have hle : B⁻¹ ≤ (‖B⁻¹‖+1)•(1 : Matrix n n ℂ) := by
    have h1 := hB.inv.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
    have h1' : B⁻¹ ≤ ‖B⁻¹‖•(1 : Matrix n n ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using h1
    have h2 : ‖B⁻¹‖•(1 : Matrix n n ℂ) ≤ (‖B⁻¹‖+1)•1 :=
      smul_le_smul_of_nonneg_right (by linarith) zero_le_one
    exact h1'.trans h2
  have hi := CStarAlgebra.ringInverse_le_ringInverse hle hB.inv.isStrictlyPositive
  simpa only [← Matrix.nonsing_inv_eq_ringInverse,inv_real_smul_one hb.ne',
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)] using hi

private theorem far_core_mem_matrixKInverseStableDomain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (α M c : ℝ) (hα : 0≤α) (hM : 0≤M) (hc : 0<c)
    (hbound : ∀ T ∈ ν.support, ‖T.val‖≤M)
    (hsmall : α*(M*c⁻¹)^2<1)
    (Y : selfAdjoint (Matrix n n ℂ))
    (hY : (M+c)•(1 : Matrix n n ℂ) ≤ Y.val) :
    Y ∈ matrixKInverseStableDomain ν α := by
  have hYpos : Y.val.PosDef := posDef_of_posDef_le_complex
    (Matrix.PosDef.one.smul (by linarith : 0<M+c)) hY
  have hgaple (T) (hT : T ∈ ν.support) : c•(1 : Matrix n n ℂ) ≤ Y.val+T.val := by
    have hneg : (-M)•(1 : Matrix n n ℂ) ≤ T.val := by
      have hTH : T.val.IsHermitian := T.property
      have hh := hTH.isSelfAdjoint.neg_algebraMap_norm_le_self
      have hm : (-M)•(1 : Matrix n n ℂ) ≤ (-‖T.val‖)•1 :=
        smul_le_smul_of_nonneg_right (by linarith [hbound T hT]) zero_le_one
      exact hm.trans (by simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using hh)
    have hh := add_le_add hY hneg
    convert! hh using 1; module
  have hgap (T) (hT : T ∈ ν.support) : (Y.val+T.val).PosDef :=
    posDef_of_posDef_le_complex (Matrix.PosDef.one.smul hc) (hgaple T hT)
  let f := fun T : selfAdjoint (Matrix n n ℂ) =>
    T.val*(Y.val+T.val)⁻¹*(1 : Matrix n n ℂ)*(Y.val+T.val)⁻¹*T.val
  have hnorm : ∀ᵐ T ∂ν, ‖f T‖ ≤ (M*c⁻¹)^2 := by
    filter_upwards [ν.support_mem_ae] with T hT
    have hi := norm_inv_le_of_scalar_gap hc (hgaple T hT)
    dsimp only [f]
    rw [Matrix.mul_one]
    calc
      _ ≤ ‖T.val‖*‖(Y.val+T.val)⁻¹‖*‖(Y.val+T.val)⁻¹‖*‖T.val‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
            (norm_nonneg _))
      _ ≤ M*c⁻¹*c⁻¹*M := by gcongr <;> exact hbound T hT
      _ = _ := by ring
  have hi : ‖∫ T, f T ∂ν‖ ≤ (M*c⁻¹)^2 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hnorm
  have hH : (matrixKInverseStability ν α Y.val 1).IsHermitian := by
    unfold matrixKInverseStability
    apply Matrix.IsHermitian.smul ?_ (IsSelfAdjoint.all α)
    apply Matrix.isHermitian_integral
    filter_upwards [ν.support_mem_ae] with T hT
    have hTH : T.val.IsHermitian := T.property
    simp only [Matrix.IsHermitian,Matrix.conjTranspose_mul,Matrix.conjTranspose_one,
      hTH.eq,(hgap T hT).inv.isHermitian.eq,Matrix.mul_assoc]
  have hnormF : ‖matrixKInverseStability ν α Y.val 1‖<1 := by
    rw [matrixKInverseStability,norm_smul,Real.norm_of_nonneg hα]
    exact (mul_le_mul_of_nonneg_left hi hα).trans_lt hsmall
  exact ⟨hYpos,hgap,1,Matrix.PosDef.one,
    posDef_one_sub_of_isHermitian_norm_lt_one hH hnormF⟩

/-- The actual source inverse-variable stable domain is connected. Compact
support constructs a common convex far-positive region, and every actual
positive certificate supplies a ray from its original point into that region.
No connectedness or inverse-branch certificate is supplied as an input.
Source: Montanari--Saeed (2026), Lemma 9.
atlas: block-wishart-variational-edges (partial) -/
theorem isConnected_matrixKInverseStableDomain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) {α : ℝ} (hα : 0≤α) :
    IsConnected (matrixKInverseStableDomain ν α) := by
  obtain ⟨M,hM,hbound⟩ := hν.isBounded.exists_pos_norm_le
  let c := α*M^2+1
  have hc : 0<c := by dsimp [c]; positivity
  have hsmall : α*(M*c⁻¹)^2<1 := by
    have he : α*(M*c⁻¹)^2=α*M^2/c^2 := by ring
    rw [he]
    apply (div_lt_one (sq_pos_of_pos hc)).mpr
    dsimp [c]
    nlinarith [sq_nonneg (α*M^2),mul_nonneg hα (sq_nonneg M)]
  let core : Set (selfAdjoint (Matrix n n ℂ)) :=
    {Y | (M+c)•(1 : Matrix n n ℂ) ≤ Y.val}
  let base : selfAdjoint (Matrix n n ℂ) := (M+c)•1
  have hbase : base ∈ core := by
    change (M+c)•(1 : Matrix n n ℂ) ≤ (M+c)•(1 : Matrix n n ℂ)
    exact le_refl _
  have hcoreSub : core ⊆ matrixKInverseStableDomain ν α := by
    intro Y hY
    exact far_core_mem_matrixKInverseStableDomain ν α M c hα hM.le hc
      (fun T hT => hbound T hT) hsmall Y hY
  have hcoreConvex : Convex ℝ core := by
    intro Y hY Z hZ a b ha hb hab
    change (M+c)•(1 : Matrix n n ℂ) ≤ Y.val at hY
    change (M+c)•(1 : Matrix n n ℂ) ≤ Z.val at hZ
    change (M+c)•(1 : Matrix n n ℂ) ≤ a•Y.val+b•Z.val
    have hh := add_le_add (smul_le_smul_of_nonneg_left hY ha)
      (smul_le_smul_of_nonneg_left hZ hb)
    rw [← add_smul,hab,one_smul] at hh
    exact hh
  refine ⟨⟨base,hcoreSub hbase⟩,?_⟩
  apply isPreconnected_of_forall base
  intro Y hY
  obtain ⟨hYpos,hgap,B,hB,hdef⟩ := hY
  let β : selfAdjoint (Matrix n n ℂ) := ⟨B,hB.isHermitian⟩
  let γ : ℝ → selfAdjoint (Matrix n n ℂ) := fun t => Y+t•β
  let ray := γ '' Ici (0 : ℝ)
  have hray : IsPreconnected ray := isPreconnected_Ici.image γ (by fun_prop)
  have hYray : Y ∈ ray := ⟨0,by simp,by simp [γ]⟩
  have hraySub : ray ⊆ matrixKInverseStableDomain ν α := by
    rintro _ ⟨t,ht,rfl⟩
    exact matrixKInverseStableDomain_certificate_ray ν hν hα Y hYpos hgap B hB hdef ht
  let t := (M+c)*(‖B⁻¹‖+1)
  have ht : 0≤t := by dsimp [t]; positivity
  have hhit : γ t ∈ core := by
    have hh := smul_le_smul_of_nonneg_left (scalar_lower_bound_of_posDef B hB) ht
    have he : t*((‖B⁻¹‖+1)⁻¹)=M+c := by
      dsimp [t]
      rw [mul_assoc,mul_inv_cancel₀ (by positivity : ‖B⁻¹‖+1≠0),mul_one]
    rw [smul_smul,he] at hh
    change (M+c)•(1 : Matrix n n ℂ) ≤ Y.val+t•B
    exact hh.trans (le_add_of_nonneg_left hYpos.posSemidef.nonneg)
  have hmeet : (ray ∩ core).Nonempty := ⟨γ t,⟨t,ht,rfl⟩,hhit⟩
  exact ⟨ray ∪ core,union_subset hraySub hcoreSub,Or.inr hbase,Or.inl hYray,
    IsPreconnected.union' hmeet hray hcoreConvex.isPreconnected⟩

end NLAlib

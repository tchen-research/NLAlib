import NLAlib.Matrix.Functions.KTransformNormalization
import NLAlib.ForMathlib.Analysis.Matrix.ScalarInverseBound
import Mathlib.Topology.Order.IntermediateValue

/-! # Native exterior norm bounds for the actual nonlinear K branch

Continuity selects the small inverse-variable solution outside a fixed
sample-dependent interval. Every resolvent and integral is the native
one from the original equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem exterior_lt_of_eventually_lt_of_ne {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) {C : ℝ}
    (hevent : ∀ᶠ y in atTop, f y<C)
    (hne : ∀ y : ℝ, 0<y → f y≠C) {y : ℝ} (hy : 0<y) : f y<C := by
  by_contra h
  have hlarge : C≤f y := le_of_not_gt h
  obtain ⟨Y,hY,hsmall⟩ := ((eventually_ge_atTop y).and hevent).exists
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hY
    (hf.mono (fun t ht => lt_of_lt_of_le hy ht.1)) ⟨hsmall.le,hlarge⟩
  exact hne t (lt_of_lt_of_le hy ht.1) hft

private theorem exterior_scalar_im (z : ℂ) :
    (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
  have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
  simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]

private theorem exterior_neg_inverse_involutive (S : M) (hS : IsUnit S) :
    -(-S⁻¹)⁻¹=S := by
  have hi : (-S⁻¹)⁻¹= -S := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.neg_mul,Matrix.mul_neg,neg_neg,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
  rw [hi,neg_neg]

private theorem exterior_kernel_inverse_bound
    (α R : ℝ) (hα : 0<α) (hR : 0<R) (z : ℂ) (X T : M)
    (hX : (imaginaryPart X : M).PosDef) (hT : T.IsHermitian)
    (hTN : ‖T‖≤R) (hfar : 4*(α+1)*R<α*|z.re|)
    (hsmall : ‖X-α•(z•1)‖≤2*α*R) :
    ‖(X-T)⁻¹‖≤((α+1)*R)⁻¹ := by
  have hunit : IsUnit (X-T) := by
    apply Matrix.isUnit_of_posDef_imaginaryPart
    simpa only [map_sub,hT.isSelfAdjoint.imaginaryPart,sub_zero] using hX
  have herror : ‖(X-T)-(α•z)•1‖≤(2*α+1)*R := by
    calc
      _ = ‖(X-α•(z•1))-T‖ := by rw [smul_assoc]; congr 1; abel
      _ ≤ ‖X-α•(z•1)‖+‖T‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hw : α*|z.re|≤‖α•z‖ := by
    rw [norm_smul,Real.norm_of_nonneg hα.le]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) hα.le
  have hgap : (2*α+1)*R<‖α•z‖ := by nlinarith
  have hbound := Matrix.norm_nonsing_inv_le_of_sub_smul_one_le
    (X-T) (α•z) ((2*α+1)*R) hunit herror hgap
  refine hbound.trans ?_
  have hpos : 0<(α+1)*R := mul_pos (by linarith) hR
  have hle : (α+1)*R≤‖α•z‖-(2*α+1)*R := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le hpos hle

private theorem exterior_averaged_kernel_bound
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν]
    (α R : ℝ) (hα : 0<α) (hR : 0<R) (z : ℂ) (S : M)
    (hS : (imaginaryPart S : M).PosDef)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (hfar : 4*(α+1)*R<α*|z.re|)
    (hsmall : ‖-S⁻¹-α•(z•1)‖≤2*α*R) :
    ‖∫ T,matrixKResolvent S T.val ∂ν‖≤R+R^2*((α+1)*R)⁻¹ := by
  let X := -S⁻¹
  have hX : (imaginaryPart X : M).PosDef := posDef_imaginaryPart_neg_matrixInverse S hS
  have hinv : -X⁻¹=S := exterior_neg_inverse_involutive S
    (Matrix.isUnit_of_posDef_imaginaryPart hS)
  have hpt : ∀ᵐ T : selfAdjoint M ∂ν,
      ‖matrixKResolvent S T.val‖≤R+R^2*((α+1)*R)⁻¹ := by
    filter_upwards [ν.support_mem_ae] with T hT
    have hTN : ‖T.val‖≤R := by simpa only [specNorm_eq_norm] using hbound T hT
    have hRN := exterior_kernel_inverse_bound α R hα hR z X T.val hX T.property hTN hfar hsmall
    have hker : matrixKResolvent S T.val=T.val+T.val*(X-T.val)⁻¹*T.val := by
      rw [← hinv]
      exact matrixKResolvent_neg_inverse_eq X T.val hX T.property
    rw [hker]
    calc
      _ ≤ ‖T.val‖+‖T.val*(X-T.val)⁻¹*T.val‖ := norm_add_le _ _
      _ ≤ ‖T.val‖+‖T.val‖*‖(X-T.val)⁻¹‖*‖T.val‖ :=
        add_le_add le_rfl ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      _ ≤ R+R*((α+1)*R)⁻¹*R := by gcongr
      _ = _ := by ring
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) hpt

private theorem exterior_inverse_center_identity
    (ν : Measure (selfAdjoint M)) (α : ℝ) (hα : α≠0) (z : ℂ) (S : M)
    (hK : matrixKTransform ν α S=z•1) :
    -S⁻¹-α•(z•1)= -(α•(∫ T,matrixKResolvent S T.val ∂ν)) := by
  have he := congrArg (fun Y : M => α•Y) hK
  rw [matrixKTransform,smul_sub,smul_smul,mul_inv_cancel₀ hα,one_smul] at he
  rw [← he]
  abel

/-- The genuine analytic K branch stays on its small inverse-variable
solution outside a uniform interval determined by the actual sample
bound. Continuity and the nonlinear equation exclude the other norm
branch; no branch-selection bound is assumed.
Source: Montanari--Saeed (2026), Lemma 1, exterior compact-support step.
atlas: block-wishart-variational-edges (partial) -/
theorem norm_neg_inverse_sub_scalar_matrixKTransform_solution_lt
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α R : ℝ) (hα : 0<α) (hR : 0<R) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (x : ℝ) (hfar : 4*(α+1)*R<α*|x|) {y : ℝ} (hy : 0<y) :
    ‖-(F ((x : ℂ)+(y : ℂ)*Complex.I))⁻¹-
      α•(((x : ℂ)+(y : ℂ)*Complex.I)•1)‖<2*α*R := by
  let z : ℝ → ℂ := fun t => (x : ℂ)+(t : ℂ)*Complex.I
  let g : ℝ → ℝ := fun t => ‖-(F (z t))⁻¹-α•((z t)•1)‖
  have hzc : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hz (t : ℝ) : (z t).im=t := by simp [z]
  have hzr (t : ℝ) : (z t).re=x := by simp [z]
  have hgc : ContinuousOn g (Ioi 0) := by
    intro t ht
    have hft := hFa (z t) (by change 0<(z t).im; rwa [hz])
    have hfu := Matrix.isUnit_of_posDef_imaginaryPart (hF (z t) (by rwa [hz])).1
    have hFc : ContinuousAt (fun s : ℝ => F (z s)) t :=
      hft.continuousAt.comp (f := z) hzc.continuousAt
    have hinv : ContinuousAt (fun s : ℝ => (F (z s))⁻¹) t :=
      (hasFDerivAt_matrixInverse (F (z t)) hfu).continuousAt.comp
        (f := fun s : ℝ => F (z s)) hFc
    have hscalar : ContinuousAt (fun s : ℝ => α•((z s)•(1 : M))) t :=
      have hs : ContinuousAt (fun s : ℝ => (z s)•(1 : M)) t :=
        hzc.continuousAt.smul continuousAt_const
      hs.const_smul α
    exact (hinv.neg.sub hscalar).norm.continuousWithinAt
  have heq (t : ℝ) (ht : 0<t) :
      g t=α*‖∫ T,matrixKResolvent (F (z t)) T.val ∂ν‖ := by
    dsimp only [g]
    rw [exterior_inverse_center_identity ν α hα.ne' (z t) (F (z t))
      (hF (z t) (by rwa [hz])).2,norm_neg,norm_smul,Real.norm_of_nonneg hα.le]
  have hlim : Tendsto (fun t : ℝ => α*(R+R^2*(α*t)⁻¹)) atTop (𝓝 (α*R)) := by
    have hi := tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hα tendsto_id)
    simpa only [Function.comp_def,id_eq,mul_zero,add_zero] using
      (tendsto_const_nhds.add (hi.const_mul (R^2))).const_mul α
  have hev : ∀ᶠ t in atTop, g t<2*α*R := by
    have hlt : α*R<2*α*R := by nlinarith
    filter_upwards [hlim.eventually (Iio_mem_nhds hlt),eventually_gt_atTop (0 : ℝ)] with t ht htp
    have hη := mul_pos hα htp
    have htarget : (α*t)•(1 : M)≤α•(imaginaryPart ((z t)•(1 : M)) : M) := by
      rw [exterior_scalar_im,hz,smul_smul]
    have hN := specNorm_integral_matrixKResolvent_of_solution_le ν hν α hα
      ((z t)•1) (F (z t)) (hF _ (by rwa [hz])).1 (hF _ (by rwa [hz])).2
      (α*t) R hη hbound htarget
    rw [heq t htp]
    exact (mul_le_mul_of_nonneg_left (by simpa only [specNorm_eq_norm] using hN) hα.le).trans_lt ht
  apply exterior_lt_of_eventually_lt_of_ne hgc hev ?_ hy
  intro t ht hlevel
  have hS := (hF (z t) (by rwa [hz])).1
  have hsmall : ‖-(F (z t))⁻¹-α•((z t)•1)‖≤2*α*R := hlevel.le
  have hN := exterior_averaged_kernel_bound ν α R hα hR (z t) (F (z t)) hS
    hbound (by rwa [hzr]) hsmall
  have hnorm : 2*α*R≤α*(R+R^2*((α+1)*R)⁻¹) := by
    rw [← hlevel,heq t ht]
    exact mul_le_mul_of_nonneg_left hN hα.le
  have hr : R^2*((α+1)*R)⁻¹<R := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (mul_pos (by linarith : 0<α+1) hR)).mpr
    nlinarith [mul_pos hα (sq_pos_of_pos hR)]
  nlinarith

/-- The actual K branch and every sample resolvent have a uniform norm
bound outside the derived exterior interval. Singular and indefinite
samples remain included. The small-branch estimate is proved by
continuity from the actual equation.
Source: Montanari--Saeed (2026), Lemma 1, compactness of the law.
atlas: block-wishart-variational-edges (partial) -/
theorem norm_inverseVariable_resolvents_matrixKTransform_solution_le_exterior
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α R : ℝ) (hα : 0<α) (hR : 0<R) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R)
    (z : ℂ) (hz : 0<z.im) (hfar : 4*(α+1)*R<α*|z.re|) :
    ‖F z‖≤((α+1)*R)⁻¹ ∧
      ∀ T ∈ ν.support, ‖(-((F z)⁻¹)-T.val)⁻¹‖≤((α+1)*R)⁻¹ := by
  have hsmall : ‖-(F z)⁻¹-α•(z•1)‖≤2*α*R := by
    have h := norm_neg_inverse_sub_scalar_matrixKTransform_solution_lt ν hν α R hα hR F hFa hF
      hbound z.re hfar hz
    simpa only [Complex.re_add_im] using h.le
  let X := -(F z)⁻¹
  have hX : (imaginaryPart X : M).PosDef :=
    posDef_imaginaryPart_neg_matrixInverse (F z) (hF z hz).1
  have hinv : -X⁻¹=F z := exterior_neg_inverse_involutive (F z)
    (Matrix.isUnit_of_posDef_imaginaryPart (hF z hz).1)
  constructor
  · have h0 := exterior_kernel_inverse_bound α R hα hR z X 0 hX Matrix.isHermitian_zero
      (by simpa only [norm_zero] using hR.le) hfar hsmall
    calc
      _ = ‖X⁻¹‖ := by rw [← hinv,norm_neg]
      _ ≤ _ := by simpa only [sub_zero] using h0
  · intro T hT
    exact exterior_kernel_inverse_bound α R hα hR z X T.val hX T.property
      (by simpa only [specNorm_eq_norm] using hbound T hT) hfar hsmall

end NLAlib

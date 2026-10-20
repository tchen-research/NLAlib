import NLAlib.Matrix.Functions.KTransformAffineBranch
import NLAlib.Matrix.Functions.KTransformOrderedImage
import NLAlib.ForMathlib.Analysis.Matrix.PositiveLimit
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-! # Genuine ordered continuation of the nonlinear K transform

Actual positive inverse-variable cones are closed under limits of
solutions. Local inverse branches and the strictly positive derivative
provide the open and nonempty parts of continuation on a positive ray.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
private abbrev KPositiveParameter := {t : ℝ // 0<t}
local notation "J" => KPositiveParameter

omit [Fintype n] [DecidableEq n] [Nonempty n] in
private theorem orderedContinuation_real_smul (t : ℝ) (H : M) :
    (t : ℂ)•H=t•H := IsScalarTower.algebraMap_smul ℂ t H

omit [Nonempty n] in
private theorem orderedContinuation_inverse_branch
    (G : ℂ → M) (S B : M) (hG0 : G 0=S) (hS : S.PosDef)
    (hGd : HasDerivAt G (-B) 0) (hB : B.PosDef)
    (hGH : ∀ᶠ t : ℝ in 𝓝 0, (G t).IsHermitian) :
    HasDerivAt (fun t : ℝ => (G t)⁻¹) (S⁻¹*B*S⁻¹) 0 ∧
      (S⁻¹*B*S⁻¹).PosDef ∧
      (∀ᶠ t : ℝ in 𝓝 0, ((G t)⁻¹).IsHermitian) := by
  have hGR : HasDerivAt (fun t : ℝ => G t) (-B) 0 := by
    have hcoe : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
      convert! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))) using 1
    have hGC : HasFDerivAt G
        ((ContinuousLinearMap.toSpanSingleton ℂ (-B)).restrictScalars ℝ) ((0 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_zero] using hGd.hasFDerivAt.restrictScalars ℝ
    convert! hGC.comp_hasDerivAt (0 : ℝ) hcoe using 1
    simp only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
      one_smul]
  have hInv : HasFDerivAt (fun X : M => X⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ M S⁻¹ S⁻¹) (G (0 : ℝ)) := by
    simpa only [Complex.ofReal_zero,hG0] using hasFDerivAt_matrixInverse S hS.isUnit
  refine ⟨?_,?_,?_⟩
  · convert! hInv.comp_hasDerivAt (0 : ℝ) hGR using 1
    simp only [_root_.neg_apply,ContinuousLinearMap.mulLeftRight_apply,
      Matrix.mul_neg,Matrix.neg_mul,neg_neg]
  · simpa only [Matrix.star_eq_conjTranspose,hS.inv.isHermitian.eq] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff hS.inv.isUnit (x := B)).mpr hB
  · exact hGH.mono fun t ht => ht.inv

private def orderedKSolvableSet (ν : Measure (selfAdjoint M)) (α : ℝ) (Y H : M) : Set J :=
  {t | ∃ Z : M, Y≤Z ∧ matrixKTransform ν α Z⁻¹=
    matrixKTransform ν α Y⁻¹-(t.val : ℂ)•H}

omit [Nonempty n] in
private theorem orderedContinuation_solvable_isClosed
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y H : M) (hY : Y.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    IsClosed (orderedKSolvableSet ν α Y H) := by
  have hc : Continuous (fun t : J => matrixKTransform ν α Y⁻¹-(t.val : ℂ)•H) := by fun_prop
  exact (isClosed_image_ordered_matrixKTransform_inverse ν hν α hα Y hY hgapY).preimage hc

private theorem orderedContinuation_solvable_nonempty
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y : selfAdjoint M) (hY : Y∈matrixKInverseStableDomain ν α)
    (H : M) (hH : H.PosDef) : (orderedKSolvableSet ν α Y.val H).Nonempty := by
  have hst : Y.val⁻¹∈matrixKStableDomain ν α := by
    rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
    exact ⟨Y,hY,rfl⟩
  obtain ⟨G,B,hGa,hG0,hB,hGd,hGH,hGeq⟩ :=
    exists_analytic_matrixKTransform_decreasing_affine_branch ν hν α hα Y.val⁻¹
      hst.1 hst.2.1 hst.2.2 H hH
  have hYY : Y.val⁻¹⁻¹=Y.val := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hY.1.isUnit)
  obtain ⟨hInv,hPos,hInvH⟩ := orderedContinuation_inverse_branch G Y.val⁻¹ B hG0 hst.1 hGd hB hGH
  have hinc := Matrix.eventually_posDef_sub_of_posDef_deriv (fun t : ℝ => (G t)⁻¹)
    (Y.val⁻¹⁻¹*B*Y.val⁻¹⁻¹) hInv hPos hInvH
  have hx : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have hx0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0 : ℝ)
    exact hx0.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t ∧ Y.val≤(G t)⁻¹ ∧
      matrixKTransform ν α ((G t)⁻¹)⁻¹=matrixKTransform ν α Y.val⁻¹-(t : ℂ)•H := by
    filter_upwards [hinc,hx.eventually hGeq,self_mem_nhdsWithin] with t ht hte htp
    refine ⟨htp,?_,?_⟩
    · have hpd : ((G t)⁻¹-Y.val).PosDef := by
        simpa only [Complex.ofReal_zero,hG0,hYY] using ht
      exact Matrix.le_iff.mpr hpd.posSemidef
    · rw [Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hte.1.1)]
      exact hte.2
  obtain ⟨t,ht,hord,heq⟩ := he.exists
  exact ⟨⟨t,ht⟩,(G t)⁻¹,hord,heq⟩

private theorem orderedContinuation_solvable_isOpen
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y : selfAdjoint M) (hY : Y∈matrixKInverseStableDomain ν α)
    (H : M) (hH : H.PosDef) : IsOpen (orderedKSolvableSet ν α Y.val H) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro t ⟨Z,hYZ,hKZ⟩
  have hZ : Z.PosDef := (hY.1.isStrictlyPositive.of_le hYZ).posDef
  let Zsa : selfAdjoint M := ⟨Z,hZ.isHermitian⟩
  have hdec : (matrixKTransform ν α Y.val⁻¹-matrixKTransform ν α Z⁻¹).PosDef := by
    rw [hKZ,sub_sub_cancel]
    rw [orderedContinuation_real_smul]
    exact hH.smul t.property
  obtain ⟨hstrict,hZstable⟩ :=
    posDef_sub_and_mem_matrixKInverseStableDomain_of_ordered_transform_decrease ν hν α hα
      Y Zsa hY.1 hY.2.1 hYZ hdec
  have hst : Z⁻¹∈matrixKStableDomain ν α := by
    rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
    exact ⟨Zsa,hZstable,rfl⟩
  obtain ⟨G,B,hGa,hG0,hB,hGd,hGH,hGeq⟩ :=
    exists_analytic_matrixKTransform_decreasing_affine_branch ν hν α hα Z⁻¹
      hst.1 hst.2.1 hst.2.2 H hH
  have hZZ : Z⁻¹⁻¹=Z := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit)
  obtain ⟨hInv,_hB,hInvH⟩ := orderedContinuation_inverse_branch G Z⁻¹ B hG0 hst.1 hGd hB hGH
  have hlim : Tendsto (fun r : ℝ => (G r)⁻¹-Y.val) (𝓝 0) (𝓝 (Z-Y.val)) := by
    simpa only [Complex.ofReal_zero,hG0,hZZ] using hInv.continuousAt.tendsto.sub_const Y.val
  have hlimH : ∀ᶠ r : ℝ in 𝓝 0, ((G r)⁻¹-Y.val).IsHermitian :=
    hInvH.mono fun _ hr => hr.sub Y.property
  have hp := hstrict.eventually_of_tendsto hlim hlimH
  have hx : Tendsto (fun u : J => ((u.val-t.val : ℝ) : ℂ)) (𝓝 t) (𝓝 (0 : ℂ)) := by
    have hcont : Continuous (fun u : J => ((u.val-t.val : ℝ) : ℂ)) := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using hcont.tendsto t
  have hr : Tendsto (fun u : J => u.val-t.val) (𝓝 t) (𝓝 0) := by
    have hcont : Continuous (fun u : J => u.val-t.val) := by fun_prop
    simpa only [sub_self] using hcont.tendsto t
  filter_upwards [hr.eventually hp,hx.eventually hGeq] with u hu hsolve
  refine ⟨(G ((u.val-t.val : ℝ) : ℂ))⁻¹,Matrix.le_iff.mpr hu.posSemidef,?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hsolve.1.1),hsolve.2,hKZ,Complex.ofReal_sub,sub_smul]
  abel

/-- Every strictly positive native K target decrease can be reached by
an actual ordered positive inverse variable. The solution and its strict
stability are constructed by compactness and local inversion on the
connected positive parameter ray. No branch existence, order-image
property, or stability conclusion is assumed.
Source: Montanari--Saeed (2026), Theorem 3, real stable-domain continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_ordered_matrixKTransform_inverse_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y : selfAdjoint M) (hY : Y∈matrixKInverseStableDomain ν α)
    (H : M) (hH : H.PosDef) :
    ∃ Z : selfAdjoint M, (Z.val-Y.val).PosDef ∧ Z∈matrixKInverseStableDomain ν α ∧
      matrixKTransform ν α Z.val⁻¹=matrixKTransform ν α Y.val⁻¹-H := by
  let : PreconnectedSpace J := Subtype.preconnectedSpace (isPreconnected_Ioi (a := (0 : ℝ)))
  have he : orderedKSolvableSet ν α Y.val H=univ :=
    (show IsClopen (orderedKSolvableSet ν α Y.val H) from
      ⟨orderedContinuation_solvable_isClosed ν hν α hα Y.val H hY.1 hY.2.1,
        orderedContinuation_solvable_isOpen ν hν α hα Y hY H hH⟩).eq_univ
          (orderedContinuation_solvable_nonempty ν hν α hα Y hY H hH)
  have hm : (⟨1,zero_lt_one⟩ : J)∈orderedKSolvableSet ν α Y.val H := by rw [he]; trivial
  obtain ⟨Z,hYZ,hKZ⟩ := hm
  have hZ : Z.PosDef := (hY.1.isStrictlyPositive.of_le hYZ).posDef
  let Zsa : selfAdjoint M := ⟨Z,hZ.isHermitian⟩
  have hKZ' : matrixKTransform ν α Z⁻¹=matrixKTransform ν α Y.val⁻¹-H := by
    simpa only [Complex.ofReal_one,one_smul] using hKZ
  have hdiff : (matrixKTransform ν α Y.val⁻¹-matrixKTransform ν α Z⁻¹).PosDef := by
    rw [hKZ',sub_sub_cancel]
    exact hH
  obtain ⟨hstrict,hstable⟩ :=
    posDef_sub_and_mem_matrixKInverseStableDomain_of_ordered_transform_decrease ν hν α hα
      Y Zsa hY.1 hY.2.1 hYZ hdiff
  exact ⟨Zsa,hstrict,hstable,hKZ'⟩

end NLAlib

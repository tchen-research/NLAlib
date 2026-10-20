import NLAlib.Matrix.Functions.KTransformAdjoint
import NLAlib.Matrix.Functions.KTransformLocalInverse
import NLAlib.Matrix.Functions.KTransformStableOpen
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Actual local real inverse paths for arbitrary Hermitian targets

The genuine complex inverse theorem gives an affine target branch.
Adjoint symmetry proves its real values, the true derivative equation
identifies its slope, and openness preserves the original stable domain.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- Every Hermitian affine target direction has a genuine local analytic
inverse through an original stable K point. Its real derivative is
Hermitian and solves the actual derivative equation; the actual nearby
real values stay in the original stable domain.
Source: Montanari--Saeed (2026), stable-domain local inversion.
atlas: block-wishart-log-potential (partial) -/
theorem exists_analytic_real_matrixKTransform_affine_branch
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : M) (hS : S ∈ matrixKStableDomain ν α)
    (H : M) (hH : H.IsHermitian) :
    ∃ (G : ℂ → M) (B : M), AnalyticAt ℂ G 0 ∧ G 0 = S ∧
      HasDerivAt G B 0 ∧ HasDerivAt (fun t : ℝ => G t) B 0 ∧ B.IsHermitian ∧
      matrixKTransformDeriv ν α S B = H ∧
      (∀ᶠ z : ℂ in 𝓝 0, G z ∈ matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z) = matrixKTransform ν α S + z • H) ∧
      ∀ᶠ t : ℝ in 𝓝 0, G t ∈ matrixKStableDomain ν α := by
  have hdom : S ∈ matrixKTransformDomain ν :=
    ⟨hS.1.isUnit, fun T hT => isUnit_matrixKDenominator S T.val hS.1 (hS.2.1 T hT)⟩
  let D := matrixKTransformDerivComplex ν α S
  have hinj : Function.Injective D :=
    injective_matrixKTransformDerivComplex_of_quadratic_pos ν hν α hα S hS.1 hS.2.1 hS.2.2
  let e : M ≃L[ℂ] M := (LinearEquiv.ofBijective D.toLinearMap
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hderiv : HasFDerivAt (matrixKTransform ν α) (e : M →L[ℂ] M) S := by
    convert! hasFDerivAt_matrixKTransform_complex ν hν α hdom using 1
  have hc := contDiffAt_matrixKTransform_complex ν hν α hdom
  let Q := hc.localInverse hderiv one_ne_zero
  let P : ℂ → M := fun z => matrixKTransform ν α S + z • H
  let G : ℂ → M := fun z => Q (P z)
  have hP0 : P 0 = matrixKTransform ν α S := by simp only [P, zero_smul, add_zero]
  have hQc := hc.to_localInverse hderiv one_ne_zero
  have hGc : ContDiffAt ℂ 1 G 0 := by
    apply ContDiffAt.comp 0 (g := Q) (f := P)
    · rwa [hP0]
    · exact contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hGa : AnalyticAt ℂ G 0 := Complex.analyticAt_iff_eventually_differentiableAt.mpr
    ((hGc.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have hG0 : G 0 = S := by
    change Q (P 0) = S
    rw [hP0]
    exact hc.localInverse_apply_image hderiv one_ne_zero
  have hcont : Tendsto G (𝓝 0) (𝓝 S) := by simpa only [hG0] using hGa.continuousAt.tendsto
  have hright := (hc.hasStrictFDerivAt' hderiv one_ne_zero).eventually_right_inverse
  have hleft : ∀ᶠ X in 𝓝 S, Q (matrixKTransform ν α X) = X :=
    (hc.hasStrictFDerivAt' hderiv one_ne_zero).eventually_left_inverse
  have hPc : Tendsto P (𝓝 0) (𝓝 (matrixKTransform ν α S)) := by
    rw [← hP0]
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hGeq : ∀ᶠ z : ℂ in 𝓝 0, G z ∈ matrixKTransformDomain ν ∧
      matrixKTransform ν α (G z) = P z := by
    filter_upwards [hcont.eventually ((isOpen_matrixKTransformDomain ν hν).mem_nhds hdom),
      hPc.eventually hright] with z hz hsolve
    exact ⟨hz, hsolve⟩
  let B := deriv G 0
  have hGd : HasDerivAt G B 0 := hGa.differentiableAt.hasDerivAt
  have hKd : HasFDerivAt (matrixKTransform ν α) D (G 0) := by
    rw [hG0]
    exact hasFDerivAt_matrixKTransform_complex ν hν α hdom
  have hcomp := hKd.comp_hasDerivAt (0 : ℂ) hGd
  have hPd : HasDerivAt P H 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).smul_const H).const_add
      (matrixKTransform ν α S) using 1
    simp only [one_smul]
  have hDE (X : M) : D X = matrixKTransformDeriv ν α S X :=
    congrArg (fun L : M →L[ℝ] M => L X)
      (matrixKTransformDerivComplex_restrictScalars ν α S)
  have hDB : matrixKTransformDeriv ν α S B = H := by
    have hEq : (fun z : ℂ => matrixKTransform ν α (G z)) =ᶠ[𝓝 (0 : ℂ)] P :=
      hGeq.mono fun _ h => h.2
    have hh := (hcomp.congr_of_eventuallyEq hEq.symm).unique hPd
    rwa [hDE] at hh
  have hU : (matrixKTransform ν α S).IsHermitian := by
    have hs := matrixKTransform_conjTranspose ν α S hdom
    rw [hS.1.isHermitian.eq] at hs
    exact hs.symm
  have hx : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hGreallim : Tendsto (fun t : ℝ => G t) (𝓝 0) (𝓝 S) := by
    simpa only [Function.comp_def] using hcont.comp hx
  have hGstarlim : Tendsto (fun t : ℝ => (G t)ᴴ) (𝓝 0) (𝓝 S) := by
    simpa only [Matrix.star_eq_conjTranspose, hS.1.isHermitian.eq] using hGreallim.star
  have hreal : ∀ᶠ t : ℝ in 𝓝 0, (G t).IsHermitian := by
    filter_upwards [hGreallim.eventually hleft, hGstarlim.eventually hleft, hx.eventually hGeq]
      with t ht1 ht2 hsolve
    have hPt : (P t).IsHermitian := hU.add (hH.smul (by simp [IsSelfAdjoint]))
    change (G t)ᴴ = G t
    calc
      _ = Q (matrixKTransform ν α (G t)ᴴ) := ht2.symm
      _ = Q (matrixKTransform ν α (G t)) := by
        rw [matrixKTransform_conjTranspose ν α (G t) hsolve.1, hsolve.2, hPt.eq]
      _ = _ := ht1
  have hGR : HasDerivAt (fun t : ℝ => G t) B 0 := by
    have hi : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
      convert! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))) using 1
    have hh : HasFDerivAt G ((ContinuousLinearMap.toSpanSingleton ℂ B).restrictScalars ℝ) (0 : ℂ) :=
      hGd.hasFDerivAt.restrictScalars ℝ
    convert! hh.comp_hasDerivAt (0 : ℝ) (f := fun t : ℝ => (t : ℂ)) hi using 1
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hBH : B.IsHermitian := by
    have hs := hGR.star
    have heq : (fun t : ℝ => star (G t)) =ᶠ[𝓝 0] (fun t : ℝ => G t) :=
      hreal.mono fun _ h => h.isSelfAdjoint.star_eq
    exact (hs.congr_of_eventuallyEq heq.symm).unique hGR
  let Ssa : selfAdjoint M := ⟨S, hS.1.isHermitian⟩
  have hpartS : selfAdjointPart ℝ S = Ssa :=
    Subtype.ext (hS.1.isHermitian.isSelfAdjoint.coe_selfAdjointPart_apply ℝ)
  have hRlim : Tendsto (fun t : ℝ => selfAdjointPart ℝ (G t)) (𝓝 0) (𝓝 Ssa) := by
    simpa only [Function.comp_def, hpartS] using
      (continuous_selfAdjointPart ℝ M).tendsto S |>.comp hGreallim
  have hstay := hRlim.eventually
    ((isOpen_matrixKStableDomain_hermitian ν hν α hα).mem_nhds hS)
  have hstable : ∀ᶠ t : ℝ in 𝓝 0, G t ∈ matrixKStableDomain ν α := by
    filter_upwards [hstay, hreal] with t ht hHt
    change (selfAdjointPart ℝ (G t) : M) ∈ matrixKStableDomain ν α at ht
    rwa [hHt.isSelfAdjoint.coe_selfAdjointPart_apply ℝ] at ht
  exact ⟨G, B, hGa, hG0, hGd, hGR, hBH, hDB, hGeq, hstable⟩

end NLAlib

import NLAlib.Matrix.Functions.KTransformComplexCalculus
import NLAlib.Matrix.Functions.KTransformHilbert
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# An actual local analytic inverse branch at a stable K-transform point

Strict Frobenius positivity on Hermitian directions implies invertibility
of the actual complex derivative on every matrix direction. The complex
inverse theorem then constructs a genuine analytic branch for scalar
spectral parameters, with all denominator neighborhoods discharged.
Global identification with the distinguished Stieltjes branch remains a
separate theorem; it is not an assumption hidden in this local result.

Source: Montanari--Saeed 2026, local inverse step in Theorem 3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology ComplexStarModule ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Strict Frobenius positivity of the true derivative on Hermitian
directions makes its genuine complex-linear derivative injective on all
matrices, through the actual real/imaginary Hermitian decomposition. -/
theorem injective_matrixKTransformDerivComplex_of_quadratic_pos
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (hpos : ∀ H : Matrix n n ℂ, H.IsHermitian → H ≠ 0 →
      0 < frobInner H (matrixKTransformDeriv ν α S H)) :
    Function.Injective (matrixKTransformDerivComplex ν α S) := by
  let D := matrixKTransformDerivComplex ν α S
  have hD (X : Matrix n n ℂ) : D X = matrixKTransformDeriv ν α S X :=
    congrArg (fun L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ => L X)
      (matrixKTransformDerivComplex_restrictScalars ν α S)
  have hherm {H : Matrix n n ℂ} (hH : H.IsHermitian) : (D H).IsHermitian := by
    rw [hD]
    exact isHermitian_matrixKTransformDeriv ν hν α hα S hS hgap hH
  have hzero (X : Matrix n n ℂ) (hX : D X = 0) : X = 0 := by
    let H : Matrix n n ℂ := realPart X
    let K : Matrix n n ℂ := imaginaryPart X
    have hH : H.IsHermitian := (realPart X).property
    have hK : K.IsHermitian := (imaginaryPart X).property
    have hDH := hherm hH
    have hDK := hherm hK
    have hs : D H + Complex.I • D K = 0 := by
      rw [← map_smul, ← map_add]
      exact (congrArg D (realPart_add_I_smul_imaginaryPart X)).trans hX
    have hsstar := congrArg Matrix.conjTranspose hs
    have hstarI : star Complex.I = -Complex.I := by simp
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hDH.eq, hDK.eq, Matrix.conjTranspose_zero, hstarI] at hsstar
    have hDH₀ : D H = 0 := by
      ext i j
      have h₁ := congrArg (fun M : Matrix n n ℂ => M i j) hs
      have h₂ := congrArg (fun M : Matrix n n ℂ => M i j) hsstar
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at h₁ h₂
      simp only [Matrix.zero_apply]
      linear_combination (1/2 : ℂ) * h₁ + (1/2 : ℂ) * h₂
    have hDK₀ : D K = 0 := by
      rw [hDH₀, zero_add] at hs
      exact (smul_eq_zero.mp hs).resolve_left Complex.I_ne_zero
    have hH₀ : H = 0 := by
      by_contra hh
      have hp := hpos H hH hh
      rw [← hD H, hDH₀, frobInner_zero_right] at hp
      exact lt_irrefl _ hp
    have hK₀ : K = 0 := by
      by_contra hh
      have hp := hpos K hK hh
      rw [← hD K, hDK₀, frobInner_zero_right] at hp
      exact lt_irrefl _ hp
    have hdec : H + Complex.I • K = X := realPart_add_I_smul_imaginaryPart X
    rw [hH₀,hK₀,smul_zero,add_zero] at hdec
    exact hdec.symm
  intro X Y hXY
  exact sub_eq_zero.mp (hzero (X-Y) (by rw [map_sub,hXY,sub_self]))

/-- A stable real solved point has an actual local complex-analytic inverse
branch. The branch solves the original K equation near the source real
parameter and stays in the true simultaneous inverse domain. This is the
local branch milestone for the block-Wishart spectral-edge theorem; no
global Stieltjes identification or variational conclusion is asserted.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_inverse_branch
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (hpos : ∀ H : Matrix n n ℂ, H.IsHermitian → H ≠ 0 →
      0 < frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (hK : matrixKTransform ν α S = (u : ℂ) • 1) :
    ∃ G : ℂ → Matrix n n ℂ, AnalyticAt ℂ G (u : ℂ) ∧ G u = S ∧
      ∀ᶠ z in 𝓝 (u : ℂ), G z ∈ matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z) = z • 1 := by
  have hdomain : S ∈ matrixKTransformDomain ν :=
    ⟨hS.isUnit, fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT)⟩
  let D := matrixKTransformDerivComplex ν α S
  have hinj : Function.Injective D :=
    injective_matrixKTransformDerivComplex_of_quadratic_pos ν hν α hα S hS hgap hpos
  let e : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ :=
    (LinearEquiv.ofBijective D.toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hderiv : HasFDerivAt (matrixKTransform ν α) (e : Matrix n n ℂ →L[ℂ] Matrix n n ℂ) S := by
    convert! hasFDerivAt_matrixKTransform_complex ν hν α hdomain using 1
  have hc := contDiffAt_matrixKTransform_complex ν hν α hdomain
  let Q := hc.localInverse hderiv one_ne_zero
  let G : ℂ → Matrix n n ℂ := fun z => Q (z • 1)
  have hQ := hc.to_localInverse hderiv one_ne_zero
  have hQc : ContinuousAt Q ((u : ℂ) • 1) := by
    rw [← hK]
    exact hQ.continuousAt
  have hG : ContDiffAt ℂ 1 G (u : ℂ) := by
    apply ContDiffAt.comp (u : ℂ) (g := Q) (f := fun z : ℂ => z • (1 : Matrix n n ℂ))
    · rwa [← hK]
    · exact contDiffAt_id.smul contDiffAt_const
  have hGa : AnalyticAt ℂ G (u : ℂ) :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      ((hG.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have hG₀ : G u = S := by
    change Q ((u : ℂ) • 1) = S
    rw [← hK]
    exact hc.localInverse_apply_image hderiv one_ne_zero
  refine ⟨G,hGa,hG₀,?_⟩
  have hcont : Tendsto G (𝓝 (u : ℂ)) (𝓝 S) := by
    simpa only [hG₀] using hGa.continuousAt.tendsto
  have heq := (hc.hasStrictFDerivAt' hderiv one_ne_zero).eventually_right_inverse
  have hZ : Tendsto (fun z : ℂ => z • (1 : Matrix n n ℂ))
      (𝓝 (u : ℂ)) (𝓝 (matrixKTransform ν α S)) := by
    rw [hK]
    exact (continuous_id.smul continuous_const).continuousAt
  filter_upwards [hcont.eventually ((isOpen_matrixKTransformDomain ν hν).mem_nhds hdomain),
    hZ.eventually heq] with z hz hsolve
  exact ⟨hz,hsolve⟩

end NLAlib

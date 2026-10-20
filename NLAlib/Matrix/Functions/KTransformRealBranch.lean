import NLAlib.Matrix.Functions.KTransformAdjoint
import NLAlib.Matrix.Functions.KTransformPositiveDerivativeInverse

/-! # Native real values of the local stable K branch

The local inverse theorem and actual adjoint symmetry force the local
analytic inverse to take Hermitian values on a real neighborhood.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

omit [Nonempty n] in
/-- A genuine local analytic inverse of the actual K transform at a
stable real point takes Hermitian values on a real neighborhood. This
reflection property follows from native adjoint symmetry and the
actual local inverse theorem.
Source: Montanari--Saeed (2026), Theorem 3, real stable continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem eventually_isHermitian_matrixKTransform_inverse_branch
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (G : ℂ → M) (hGa : AnalyticAt ℂ G (u : ℂ)) (hG0 : G u=S)
    (hGeq : ∀ᶠ z in 𝓝 (u : ℂ), G z∈matrixKTransformDomain ν ∧
      matrixKTransform ν α (G z)=z•1) :
    ∀ᶠ x : ℝ in 𝓝 u, (G x).IsHermitian := by
  have hdom : S∈matrixKTransformDomain ν :=
    ⟨hS.isUnit,fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT)⟩
  let D := matrixKTransformDerivComplex ν α S
  have hinj : Function.Injective D :=
    injective_matrixKTransformDerivComplex_of_quadratic_pos ν hν α hα S hS hgap hpos
  let e : M ≃L[ℂ] M := (LinearEquiv.ofBijective D.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hderiv : HasFDerivAt (matrixKTransform ν α) (e : M →L[ℂ] M) S := by
    convert! hasFDerivAt_matrixKTransform_complex ν hν α hdom using 1
  have hc := contDiffAt_matrixKTransform_complex ν hν α hdom
  have hs := hc.hasStrictFDerivAt' hderiv one_ne_zero
  let Q := hs.localInverse (matrixKTransform ν α) e S
  have hleft : ∀ᶠ X in 𝓝 S, Q (matrixKTransform ν α X)=X := hs.eventually_left_inverse
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 u) (𝓝 (u : ℂ)) :=
    Complex.continuous_ofReal.tendsto u
  have hGlim : Tendsto (fun x : ℝ => G x) (𝓝 u) (𝓝 S) := by
    simpa only [hG0,Function.comp_def] using hGa.continuousAt.tendsto.comp hx
  have hGstar : Tendsto (fun x : ℝ => (G x)ᴴ) (𝓝 u) (𝓝 S) := by
    simpa only [Matrix.star_eq_conjTranspose,hS.isHermitian.eq] using hGlim.star
  filter_upwards [hGlim.eventually hleft,hGstar.eventually hleft,hx.eventually hGeq]
    with x hx1 hx2 hsolve
  change (G x)ᴴ=G x
  calc
    _ = Q (matrixKTransform ν α (G x)ᴴ) := hx2.symm
    _ = Q (matrixKTransform ν α (G x)) := by
      rw [matrixKTransform_conjTranspose ν α (G x) hsolve.1,hsolve.2]
      simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
        Complex.star_def,Complex.conj_ofReal]
    _ = _ := hx1

/-- A stable real solution has a genuine analytic local inverse with a
strictly positive derivative and Hermitian values on a real
neighborhood. Each property is derived from the original nonlinear K
equation and its actual stable Frobenius test.
Source: Montanari--Saeed (2026), Theorem 3, stable real branch.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_real_matrixKTransform_inverse_branch
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (hK : matrixKTransform ν α S=(u : ℂ)•1) :
    ∃ (G : ℂ → M) (B : M), AnalyticAt ℂ G (u : ℂ) ∧ G u=S ∧ B.PosDef ∧
      HasDerivAt G B (u : ℂ) ∧
      (∀ᶠ x : ℝ in 𝓝 u, (G x).IsHermitian) ∧
      ∀ᶠ z in 𝓝 (u : ℂ), G z∈matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z)=z•1 := by
  obtain ⟨G,B,hGa,hG0,hB,hGd,hGeq⟩ :=
    exists_analytic_matrixKTransform_inverse_branch_posDef_deriv ν hν α hα S hS hgap hpos u hK
  exact ⟨G,B,hGa,hG0,hB,hGd,
    eventually_isHermitian_matrixKTransform_inverse_branch ν hν α hα S hS hgap hpos
      u G hGa hG0 hGeq,hGeq⟩

end NLAlib

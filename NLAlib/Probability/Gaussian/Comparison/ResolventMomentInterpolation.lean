import NLAlib.Probability.Gaussian.Comparison.ResamplingInterpolation
import NLAlib.Matrix.Functions.ResolventMomentDerivativeBounds

/-!
# The actual normalized mixed-moment interpolation derivative

Prerequisite for
`independent-sum-spectrum-universality`. The existing scalar resampling
identity is instantiated with the actual complex normalized trace; its
analytic hypotheses follow from Hermitian reconstruction and nonreal shifts.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Sections 6.3–6.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The source derivative is an actual full-covariance expectation identity
for the native complex normalized mixed trace, without assumed differentiability
or derivative-bound premises. -/
theorem hasDerivAt_resamplingInterpolation_normalizedTrace_mixed_resolvent
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q i),
          (fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q j);
          resamplingTripleMeasure ν])
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let Φ : E → ℂ := fun x => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)
    let f := fderiv ℝ Φ
    let df := fderiv ℝ f
    let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    HasDerivAt (resamplingInterpolation ν γ Φ)
      (((Fintype.card ι : ℝ) / (4 * a)) •
          (∫ q, (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
              f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
            (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            ∂(resamplingTripleMeasure ν).prod γ) -
        ((Fintype.card ι : ℝ) / 4) •
          ∫ q, df (resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2)
            (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            ∂(resamplingTripleMeasure ν).prod γ) t := by
  dsimp only
  let Φ : E → ℂ := fun x => normalizedTrace
    (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)
  let f := fderiv ℝ Φ
  let df := fderiv ℝ f
  let B : E →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ)).flip
  have hc : ContDiff ℝ ⊤ Φ :=
    contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p
  have hfc : ContDiff ℝ ⊤ f := hc.fderiv_right (by simp)
  have hdfc : ContDiff ℝ ⊤ df := hfc.fderiv_right (by simp)
  have hΦ (y : E) : HasFDerivAt Φ (B.flip (f y)) y := by
    simpa only [B, ContinuousLinearMap.flip_flip, ContinuousLinearMap.id_apply, f] using!
      (hc.differentiable (by simp) y).hasFDerivAt
  have hf (y : E) : HasFDerivAt f (df y) y :=
    (hfc.differentiable (by simp) y).hasFDerivAt
  let C0 : ℝ := |ζ.im|⁻¹ ^ (2 * p)
  let C1 : ℝ := ((2 * p : ℕ) : ℝ) * |ζ.im|⁻¹ ^ (2 * p + 1) * ‖L‖
  let C2 : ℝ := ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    |ζ.im|⁻¹ ^ (2 * p + 2) * ‖L‖ ^ 2
  have hΦb (y : E) : ‖Φ y‖ ≤ C0 :=
    norm_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p y
  have hfb (y : E) : ‖f y‖ ≤ C1 :=
    norm_fderiv_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p y
  have hdfb (y : E) : ‖df y‖ ≤ C2 := by
    change ‖fderiv ℝ (fderiv ℝ Φ) y‖ ≤ C2
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ Φ), norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_two_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p y
  simpa only [B, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply,
    Φ, f, df] using!
    hasDerivAt_resamplingInterpolation ν hν γ hγ hmean hcov Φ f df B
      hΦ hf hdfc.continuous C0 C1 C2 hΦb hfb hdfb ht ht1

end NLAlib

import NLAlib.Probability.Gaussian.Comparison.CenteredMatrixLaw
import NLAlib.Probability.Gaussian.Comparison.ResolventMomentPath

/-!
# Actual matrix-law endpoints of resolvent Gram-moment interpolation

The coordinate interpolation endpoints are precisely the actual independent
matrix-sum and mean-matched Gaussian Gram-moment expectations. The deterministic
offset is kept outside the random square mass. Empty matrix dimensions are
included using the native normalized zero trace.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- At time one the actual coordinate Gram-moment interpolation equals the
original independent matrix-sum moment expectation. Empty dimensions and
moment order zero are included. -/
theorem resamplingInterpolation_one_matrix_resolventEvenMoment_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (γ : Measure E) [IsProbabilityMeasure γ]
    (A₀ : M) (hA₀ : A₀.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates) γ
      (fun x => resolventEvenMoment (A₀ + L x) ζ p) 1 =
      ∫ x : ι → M, resolventEvenMoment (A₀ + ∑ i, x i) ζ p ∂Measure.pi ν := by
  cases isEmpty_or_nonempty n with
  | inl hn => simp [resamplingInterpolation, resolventEvenMoment, normalizedTrace]
  | inr hn =>
    have (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
      (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
    let Φ : E → ℝ := fun x => resolventEvenMoment (A₀ + L x) ζ p
    have hΦ : Continuous Φ :=
      (contDiff_resolventEvenMoment_coordinate A₀ hA₀ ζ hζ p (r := ⊤)).continuous
    rw [resamplingInterpolation_one _ γ _ hΦ]
    calc
      _ = ∫ x : ι → M, Φ (matrixRealCoordinates (∑ i, x i)) ∂Measure.pi ν :=
        ((identDistrib_resamplingTripleOriginal_matrixRealCoordinates_sum ν).comp hΦ.measurable).integral_eq
      _ = _ := integral_congr_ae ((ae_isHermitian_sum_pi ν hν).mono fun x hx => by
        dsimp only [Φ]
        rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hx])

open scoped Matrix.Norms.L2Operator in
/-- At time zero the actual coordinate Gram-moment interpolation equals the
Gaussian matrix moment expectation when the actual matrix means agree.
Empty dimensions and moment order zero are included. -/
theorem resamplingInterpolation_zero_matrix_resolventEvenMoment_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : M → M) 3 (ν i))
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ)
    (hHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates)
      (centeredMatrixCoordinateLaw ρ) (fun x => resolventEvenMoment (A₀ + L x) ζ p) 0 =
      ∫ A : M, resolventEvenMoment A ζ p ∂ρ := by
  cases isEmpty_or_nonempty n with
  | inl hn => simp [resamplingInterpolation, resolventEvenMoment, normalizedTrace]
  | inr hn =>
    have (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
      (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
    have := hρ.isProbabilityMeasure
    have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
    have := hγ.isProbabilityMeasure
    let Φ : E → ℝ := fun x => resolventEvenMoment (A₀ + L x) ζ p
    have hΦ : Continuous Φ :=
      (contDiff_resolventEvenMoment_coordinate A₀ hA₀ ζ hζ p (r := ⊤)).continuous
    let m : E := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure
      (fun i => (ν i).map matrixRealCoordinates)
    have hm : m + matrixRealCoordinates A₀ = ∫ A : M, matrixRealCoordinates A ∂ρ := by
      calc
        _ = matrixRealCoordinates ((∫ x : ι → M, ∑ i, x i ∂Measure.pi ν) + A₀) := by
          dsimp only [m]
          rw [integral_resamplingTripleOriginal_matrixRealCoordinates ν hν, map_add]
        _ = matrixRealCoordinates (∫ A : M, A ∂ρ) := by rw [hmean, add_comm A₀]
        _ = _ := ((matrixRealCoordinatesContinuousLinearEquiv
          (m := n) (n := n)).toContinuousLinearMap.integral_comp_comm
            (integrable_id_of_hasGaussianLaw_matrixRealCoordinates ρ hρ)).symm
    rw [resamplingInterpolation_zero _ _ _ hΦ]
    change (∫ z : E, Φ (m + z) ∂centeredMatrixCoordinateLaw ρ) = _
    have hshift : Continuous (fun z : E => Φ (m + z)) := hΦ.comp (by fun_prop)
    have ht := (hasLaw_centeredMatrixCoordinates ρ).integral_comp hshift.aestronglyMeasurable
    rw [← ht]
    apply integral_congr_ae (hHerm.mono fun A hA => ?_)
    change Φ (m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ)) = _
    have he : m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ) =
        matrixRealCoordinates A - matrixRealCoordinates A₀ := by rw [← hm]; abel
    rw [he]
    dsimp only [Φ]
    rw [map_sub, hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA,
      hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA₀]
    congr 1
    abel

end NLAlib

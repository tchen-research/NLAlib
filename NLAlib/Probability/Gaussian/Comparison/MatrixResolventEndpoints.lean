import NLAlib.Probability.Gaussian.Comparison.CenteredMatrixLaw
import NLAlib.Probability.Gaussian.Comparison.ResamplingInterpolation
import NLAlib.Matrix.Functions.ResolventCoordinateOperator

/-! # Matrix-valued resolvent endpoints of the actual interpolation

The full-coordinate interpolation endpoints are the genuine independent
matrix-sum and matching Gaussian matrix resolvent expectations. The only
support restriction is almost-everywhere Hermitian support of the laws.
The deterministic offset is kept separate from the random square mass.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Section 6.4,
the endpoint laws in the proof of Lemma 6.11.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- The actual time-one coordinate interpolation is the original independent
Hermitian matrix-sum resolvent expectation.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem resamplingInterpolation_one_matrix_resolvent_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (γ : Measure E) [IsProbabilityMeasure γ]
    (A₀ : M) (hA₀ : A₀.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates) γ
      (hermitianCoordinateResolvent A₀ ζ) 1 =
      ∫ x : ι → M, resolvent (A₀ + ∑ i, x i) ζ ∂Measure.pi ν := by
  have (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  have hΦ : Continuous (hermitianCoordinateResolvent A₀ ζ) :=
    continuous_hermitianCoordinateResolvent A₀ hA₀ ζ hζ
  rw [resamplingInterpolation_one _ γ _ hΦ]
  calc
    _ = ∫ x : ι → M,
        hermitianCoordinateResolvent A₀ ζ (matrixRealCoordinates (∑ i, x i)) ∂Measure.pi ν :=
      ((identDistrib_resamplingTripleOriginal_matrixRealCoordinates_sum ν).comp hΦ.measurable).integral_eq
    _ = _ := integral_congr_ae ((ae_isHermitian_sum_pi ν hν).mono fun x hx => by
      dsimp only [hermitianCoordinateResolvent]
      rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hx])

open scoped Matrix.Norms.L2Operator in
/-- The actual time-zero coordinate interpolation is the Gaussian matrix
resolvent expectation when the actual matrix means agree.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem resamplingInterpolation_zero_matrix_resolvent_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : M → M) 3 (ν i))
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ)
    (hHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates)
      (centeredMatrixCoordinateLaw ρ) (hermitianCoordinateResolvent A₀ ζ) 0 =
      ∫ A : M, resolvent A ζ ∂ρ := by
  have (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  have := hρ.isProbabilityMeasure
  have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
  have := hγ.isProbabilityMeasure
  have hΦ : Continuous (hermitianCoordinateResolvent A₀ ζ) :=
    continuous_hermitianCoordinateResolvent A₀ hA₀ ζ hζ
  let m : E := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure
    (fun i => (ν i).map matrixRealCoordinates)
  have hm : m + matrixRealCoordinates A₀ = ∫ A : M, matrixRealCoordinates A ∂ρ := by
    calc
      _ = matrixRealCoordinates ((∫ x : ι → M, ∑ i, x i ∂Measure.pi ν) + A₀) := by
        dsimp [m]
        rw [integral_resamplingTripleOriginal_matrixRealCoordinates ν hν, map_add]
      _ = matrixRealCoordinates (∫ A : M, A ∂ρ) := by rw [hmean, add_comm A₀]
      _ = _ := ((matrixRealCoordinatesContinuousLinearEquiv
        (m := n) (n := n)).toContinuousLinearMap.integral_comp_comm
          (integrable_id_of_hasGaussianLaw_matrixRealCoordinates ρ hρ)).symm
  rw [resamplingInterpolation_zero _ _ _ hΦ]
  change (∫ z : E, hermitianCoordinateResolvent A₀ ζ (m + z)
    ∂centeredMatrixCoordinateLaw ρ) = _
  have hshift : Continuous (fun z : E => hermitianCoordinateResolvent A₀ ζ (m + z)) :=
    hΦ.comp (by fun_prop)
  have ht := (hasLaw_centeredMatrixCoordinates ρ).integral_comp hshift.aestronglyMeasurable
  rw [← ht]
  apply integral_congr_ae (hHerm.mono fun A hA => ?_)
  change hermitianCoordinateResolvent A₀ ζ
    (m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ)) = _
  have he : m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ) =
      matrixRealCoordinates A - matrixRealCoordinates A₀ := by rw [← hm]; abel
  rw [he]
  dsimp only [hermitianCoordinateResolvent]
  rw [map_sub, hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA,
    hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA₀]
  congr 1
  abel

end NLAlib

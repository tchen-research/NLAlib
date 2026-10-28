import NLAlib.Probability.Transforms.ChebyshevKernelMeasure
import NLAlib.Probability.Transforms.TensorChebyshevMomentWasserstein
import NLAlib.ForMathlib.MeasureTheory.CompactWassersteinTriangle

/-!
# Tensor smoothing of an ambient cube law

Lift a law supported on the closed cube to the cube subtype, apply the actual
positive Jackson kernel, and compose its displacement with a moment bound.
-/

noncomputable section
open MeasureTheory
namespace NLAlib
variable {d : ℕ}

/-- The squared normalized tensor discrepancies are symmetric in the two laws. -/
theorem tensorChebyshevMomentError_comm (μ ν : Measure (EuclideanSpace ℝ (Fin d))) (M : ℕ) :
    tensorChebyshevMomentError μ ν M = tensorChebyshevMomentError ν μ M := by
  unfold tensorChebyshevMomentError
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  unfold tensorChebyshevMomentDiscrepancy
  ring

/-- The native subtype law of a measure supported on the Chebyshev cube. -/
def chebyshevCubeLift (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (chebyshevCube (Fin d)) := μ.comap Subtype.val

/-- A supported probability law remains a probability law under the lift. -/
theorem isProbabilityMeasure_chebyshevCubeLift
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d)) :
    IsProbabilityMeasure (chebyshevCubeLift μ) :=
  (MeasurableEmbedding.subtype_coe isCompact_chebyshevCube.measurableSet).isProbabilityMeasure_comap
    (by simpa using hμ)

/-- Mapping the lift back to the ambient Euclidean space exactly returns the law. -/
theorem map_chebyshevCubeLift
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d)) :
    (chebyshevCubeLift μ).map Subtype.val = μ := by
  rw [chebyshevCubeLift, map_comap_subtype_coe isCompact_chebyshevCube.measurableSet,
    Measure.restrict_eq_self_of_ae_mem hμ]

/-- The actual smoothing law is supported on the closed cube. -/
theorem ae_mem_chebyshevCube_tensorChebyshevSmoothedLaw
    (μ : Measure (chebyshevCube (Fin d))) [IsProbabilityMeasure μ] (M : ℕ) :
    ∀ᵐ x ∂tensorChebyshevSmoothedLaw μ M, x ∈ chebyshevCube (Fin d) := by
  rw [tensorChebyshevSmoothedLaw_eq_map_withDensity, ae_map_iff
    (PiLp.continuous_toLp 2 _).measurable.aemeasurable]
  · exact (withDensity_absolutelyContinuous _ _).ae_le ae_mem_chebyshevCube
  · exact isCompact_chebyshevCube.measurableSet

/-- Moment discrepancy followed by actual positive smoothing has a genuine
transport bound. The explicit constant is `18d/M` in Euclidean dimension `d`. -/
theorem wassersteinEDistOne_tensorChebyshevSmoothedLaw_le_momentError
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d))
    (hν : ∀ᵐ x ∂ν, x ∈ chebyshevCube (Fin d)) {M : ℕ} (hM : 1 ≤ M) :
    wassersteinEDistOne μ (tensorChebyshevSmoothedLaw (chebyshevCubeLift ν) M) ≤
      ENNReal.ofReal (18*d/M + Real.sqrt ((d:ℝ)*Real.pi^d/2)*tensorChebyshevMomentError μ ν M) := by
  have := isProbabilityMeasure_chebyshevCubeLift ν hν
  have hsm := wassersteinEDistOne_tensorChebyshevSmoothedLaw_le (chebyshevCubeLift ν) hM
  rw [map_chebyshevCubeLift ν hν] at hsm
  simp only [Fintype.card_fin] at hsm
  have he : 0 ≤ tensorChebyshevMomentError μ ν M := Real.sqrt_nonneg _
  have hh := wassersteinEDistOne_le_add_of_ae_mem_compact μ ν
    (tensorChebyshevSmoothedLaw (chebyshevCubeLift ν) M) isCompact_chebyshevCube hμ hν
    (ae_mem_chebyshevCube_tensorChebyshevSmoothedLaw _ M)
    (by positivity : 0 ≤ 12*(d:ℝ)/M + Real.sqrt ((d:ℝ)*Real.pi^d/2)*tensorChebyshevMomentError μ ν M)
    (by positivity : 0 ≤ 6*(d:ℝ)/M)
    (wassersteinEDistOne_le_tensorChebyshevMomentError μ ν hμ hν hM) hsm
  convert hh using 1
  congr 1
  ring

end NLAlib

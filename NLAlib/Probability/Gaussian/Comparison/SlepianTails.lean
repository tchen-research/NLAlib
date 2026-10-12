import NLAlib.ForMathlib.MeasureTheory.TailComparison
import NLAlib.Probability.Gaussian.Comparison.Slepian
/-!
# Slepian comparison for nonstrict upper tails

The base theorem compares strict tails. Continuity from above
(`measure_ge_le_of_measure_gt_le`, `NLAlib.ForMathlib.MeasureTheory.TailComparison`) also gives
the catalogue's nonstrict tails, including Gaussian vectors with atoms caused by degenerate
coordinates. Equal coordinate variances remain essential. Atlas: `slepian`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLAlib

/-- **Slepian's nonstrict tail comparison.** For finite centred Gaussian vectors with
equal coordinate variances and dominated increments, `P(max X ≥ τ) ≤ Q(max Y ≥ τ)`.
Degenerate Gaussian laws are included. Slepian 1962; Vershynin 2018, Theorem 7.2.1;
atlas `slepian`.
atlas: slepian -/
theorem slepian_inequality_ge {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P)
    (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤
      ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ ≤ ⨆ t, X t ω} ≤ Q {ω | τ ≤ ⨆ t, Y t ω} := by
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  apply measure_ge_le_of_measure_gt_le
    (AEMeasurable.iSup fun t => (hX.eval t).aemeasurable)
    (AEMeasurable.iSup fun t => (hY.eval t).aemeasurable)
  exact slepian_inequality X Y hX hY hX0 hY0 hvar hinc

end NLAlib

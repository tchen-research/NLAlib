import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite probability laws for sampling with replacement

A nonnegative finite probability vector defines an actual probability measure,
whose expectations are weighted finite sums. Product laws give independent draws.
Sources: operator re-derivations `sa:leverage` and `sa:amm`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace NLAlib

/-- The probability mass function specified by a finite nonnegative vector
summing to one. Source: operator re-derivations `sa:leverage`, `sa:amm`. -/
def finiteSamplingPMF {ι : Type*} [Fintype ι] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i => (p i : ℝ≥0∞)) (by exact_mod_cast hp)

/-- The discrete probability measure with masses `p i`.
Source: operator re-derivations `sa:leverage`, `sa:amm`. -/
def finiteSamplingLaw {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) : Measure ι :=
  (finiteSamplingPMF p hp).toMeasure

/-- A finite sampling law is a probability measure. Source: the PMF construction;
supports `leverage-sampling-ose` and `amm-sampling`. -/
instance finiteSamplingLaw_isProbabilityMeasure {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteSamplingLaw p hp) := by
  unfold finiteSamplingLaw
  infer_instance

/-- Sampling expectations are the weighted finite sum, with zero masses
contributing zero. Source: operator re-derivations `sa:leverage`, `sa:amm`. -/
theorem integral_finiteSamplingLaw {ι E : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (f : ι → E) :
    ∫ i, f i ∂finiteSamplingLaw p hp = ∑ i, (p i : ℝ) • f i := by
  rw [finiteSamplingLaw, PMF.integral_eq_sum]
  simp [finiteSamplingPMF]

/-- The mass of a sampled index is precisely its specified probability.
Source: operator re-derivations `sa:leverage`, `sa:amm`. -/
theorem finiteSamplingLaw_singleton {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (i : ι) :
    finiteSamplingLaw p hp {i} = p i := by
  rw [finiteSamplingLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  simp [finiteSamplingPMF]

end NLAlib

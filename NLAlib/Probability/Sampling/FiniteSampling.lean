import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite probability laws for sampling with replacement

A nonnegative finite probability vector defines a probability measure,
whose expectations are weighted finite sums. Product laws give independent draws.
Source: Drineas–Kannan–Mahoney 2006, *SIAM J. Comput.* 36 (sampling-based matrix multiplication).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace NLAlib

/-- Normalize real finite weights to nonnegative masses. The definition is total;
its probability-vector theorem assumes nonnegative weights with positive total mass. -/
def normalizedSamplingProbabilities {ι : Type*} [Fintype ι] (u : ι → ℝ) : ι → ℝ≥0 :=
  fun i => Real.toNNReal (u i / ∑ j, u j)

/-- Nonnegative finite weights with positive total mass normalize to a probability
vector. Zero weights remain zero, so empty supports are never assigned a false law. -/
theorem sum_normalizedSamplingProbabilities {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (ht : 0 < ∑ i, u i) :
    ∑ i, normalizedSamplingProbabilities u i = 1 := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, NNReal.coe_one, normalizedSamplingProbabilities]
  simp_rw [Real.coe_toNNReal _ (div_nonneg (hu _) ht.le)]
  rw [← Finset.sum_div, div_self ht.ne']

/-- Each normalized finite mass is the original weight divided by total weight,
on the intended nonnegative, positive-mass domain. -/
theorem coe_normalizedSamplingProbabilities {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (ht : 0 < ∑ i, u i) (i : ι) :
    (normalizedSamplingProbabilities u i : ℝ) = u i / ∑ j, u j :=
  Real.coe_toNNReal _ (div_nonneg (hu i) ht.le)

/-- The occurrence count of an index in a finite sample list. -/
def sampleCount {ι : Type*} [DecidableEq ι] {s : ℕ} (ω : Fin s → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun j => ω j = i)).card

/-- Summing over a sample list agrees with grouping its entries by occurrence count.
This is the deterministic realization bridge between list and count-vector algorithms. -/
theorem sum_sampleCount_nsmul {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] {s : ℕ} (ω : Fin s → ι) (f : ι → M) :
    (∑ i, sampleCount ω i • f i) = ∑ j, f (ω j) := by
  simpa only [sampleCount, Finset.sum_const] using
    Finset.sum_fiberwise' (Finset.univ : Finset (Fin s)) ω f

/-- The number of distinct sampled indices never exceeds the number of draws. -/
theorem card_sampleCount_support_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (ω : Fin s → ι) :
    (Finset.univ.filter (fun i => sampleCount ω i ≠ 0)).card ≤ s := by
  have he : Finset.univ.filter (fun i => sampleCount ω i ≠ 0) = Finset.univ.image ω := by
    ext i
    simp [sampleCount]
  rw [he]
  exact Finset.card_image_le.trans (by simp)

/-- The probability mass function specified by a finite nonnegative vector
summing to one. Source: Drineas–Kannan–Mahoney 2006, §4. -/
def finiteSamplingPMF {ι : Type*} [Fintype ι] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i => (p i : ℝ≥0∞)) (by exact_mod_cast hp)

/-- The discrete probability measure with masses `p i`.
Source: Drineas–Kannan–Mahoney 2006, §4. -/
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
contributing zero. Source: Drineas–Kannan–Mahoney 2006, §4. -/
theorem integral_finiteSamplingLaw {ι E : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (f : ι → E) :
    ∫ i, f i ∂finiteSamplingLaw p hp = ∑ i, (p i : ℝ) • f i := by
  rw [finiteSamplingLaw, PMF.integral_eq_sum]
  simp [finiteSamplingPMF]

/-- The mass of a sampled index is precisely its specified probability.
Source: Drineas–Kannan–Mahoney 2006, §4. -/
theorem finiteSamplingLaw_singleton {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (i : ι) :
    finiteSamplingLaw p hp {i} = p i := by
  rw [finiteSamplingLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  simp [finiteSamplingPMF]

end NLAlib

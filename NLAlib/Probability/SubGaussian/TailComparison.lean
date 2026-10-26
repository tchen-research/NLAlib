import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

/-!
# Tail comparison from means and a Gaussian lower tail

Two observables with the same Gaussian concentration scale have comparable
upper tails once their means are comparable and the smaller observable has
one scalar Gaussian lower tail. This elementary small/large threshold
argument is used in Latała--van Handel--Youssef, arXiv:1711.00807v2,
Corollary 1.4.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- The positive probability supplied by concentration below half a mean
which is at least `κ` times the entry scale. -/
def gaussianHalfMeanProbability (κ : ℝ) : ℝ := 1 - Real.exp (-(κ ^ 2 / 16))

/-- A strictly positive mean-to-scale ratio gives a strictly positive
universal half-mean probability. -/
theorem gaussianHalfMeanProbability_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < gaussianHalfMeanProbability κ := by
  unfold gaussianHalfMeanProbability
  have h := Real.exp_lt_one_iff.mpr
    (neg_neg_of_pos (show 0 < κ ^ 2 / 16 by positivity))
  linarith

/-- An explicit constant for transferring a Gaussian upper tail to an
observable with comparable mean and a scalar Gaussian lower tail. -/
def gaussianTailComparisonConstant (A κ c : ℝ) : ℝ :=
  4 * A + 4 + (gaussianHalfMeanProbability κ)⁻¹ + c⁻¹

/-- The tail-comparison constant also dominates the expectation-comparison
constant whenever the latter is at least one. -/
theorem le_gaussianTailComparisonConstant {A κ c : ℝ} (hA : 1 ≤ A)
    (hκ : 0 < κ) (hc : 0 < c) : A ≤ gaussianTailComparisonConstant A κ c := by
  have hδ := inv_nonneg.mpr (gaussianHalfMeanProbability_pos hκ).le
  have hci := inv_nonneg.mpr hc.le
  unfold gaussianTailComparisonConstant
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Concentration gives a positive probability of exceeding half the
actual mean, uniformly when the mean dominates the Gaussian scale. -/
theorem gaussianHalfMeanProbability_le_measure_ge_half_mean
    {Y : Ω → ℝ} {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ)
    (h : HasSubgaussianMGF (fun ω => Y ω - ∫ y, Y y ∂μ)
      ⟨2 * m ^ 2, by positivity⟩ μ)
    (hmean : κ * m ≤ ∫ y, Y y ∂μ) :
    gaussianHalfMeanProbability κ ≤ μ.real {ω | (∫ y, Y y ∂μ) / 2 ≤ Y ω} := by
  let a := ∫ y, Y y ∂μ
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hκ hm) hmean
  have hYm : AEMeasurable Y μ := by
    convert h.aemeasurable.add_const a using 1
    funext ω
    dsimp [a]
    ring
  have htail := h.neg.measure_ge_le (show 0 ≤ a / 2 by positivity)
  have hmono : μ.real {ω | Y ω < a / 2} ≤
      μ.real {ω | a / 2 ≤ -(Y ω - a)} :=
    measureReal_mono (fun ω hω => by dsimp at hω ⊢; linarith) (by finiteness)
  have hexp : Real.exp (-(a / 2) ^ 2 / (2 * (2 * m ^ 2))) ≤
      Real.exp (-(κ ^ 2 / 16)) := by
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ (le_of_lt (mul_pos hκ hm)) hmean 2
    dsimp [a] at *
    apply (div_le_iff₀ (show 0 < 2 * (2 * m ^ 2) by positivity)).mpr
    nlinarith [hsq]
  have hbad : μ.real {ω | Y ω < a / 2} ≤ Real.exp (-(κ ^ 2 / 16)) :=
    hmono.trans (htail.trans hexp)
  have hcomp := measureReal_add_measureReal_compl₀
    (nullMeasurableSet_le aemeasurable_const hYm :
      NullMeasurableSet {ω | a / 2 ≤ Y ω} μ)
  have heq : {ω | a / 2 ≤ Y ω}ᶜ = {ω | Y ω < a / 2} := by ext ω; simp
  rw [heq, probReal_univ] at hcomp
  unfold gaussianHalfMeanProbability
  change 1 - Real.exp (-(κ ^ 2 / 16)) ≤ μ.real {ω | a / 2 ≤ Y ω}
  linarith

/-- Comparable means and a scalar Gaussian lower tail transfer all upper
tails between two observables with the same centered Gaussian proxy.
The conclusion has one constant at every nonnegative threshold. -/
theorem measure_ge_le_mul_measure_ge_div_of_gaussian_concentration
    {X Y : Ω → ℝ} {A κ c m : ℝ} (hA : 1 ≤ A) (hκ : 0 < κ)
    (hc : 0 < c) (hm : 0 < m)
    (hX : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ)
      ⟨2 * m ^ 2, by positivity⟩ μ)
    (hY : HasSubgaussianMGF (fun ω => Y ω - ∫ y, Y y ∂μ)
      ⟨2 * m ^ 2, by positivity⟩ μ)
    (hmean : (∫ y, X y ∂μ) ≤ A * ∫ y, Y y ∂μ)
    (hscale : κ * m ≤ ∫ y, Y y ∂μ)
    (hlower : ∀ u : ℝ, 0 ≤ u → c * Real.exp (-(u / m) ^ 2) ≤ μ.real {ω | u ≤ Y ω})
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ gaussianTailComparisonConstant A κ c *
      μ.real {ω | t / gaussianTailComparisonConstant A κ c ≤ Y ω} := by
  let C := gaussianTailComparisonConstant A κ c
  let a := ∫ y, Y y ∂μ
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hκ hm) hscale
  have hδ := gaussianHalfMeanProbability_pos hκ
  have hAi : 0 ≤ 4 * A := by positivity
  have hCi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hδi : 0 ≤ (gaussianHalfMeanProbability κ)⁻¹ := inv_nonneg.mpr hδ.le
  have hC4 : 4 ≤ C := by dsimp [C, gaussianTailComparisonConstant]; linarith
  have hCA : 4 * A ≤ C := by dsimp [C, gaussianTailComparisonConstant]; linarith
  have hCδ : (gaussianHalfMeanProbability κ)⁻¹ ≤ C := by
    dsimp [C, gaussianTailComparisonConstant]; linarith
  have hCc : c⁻¹ ≤ C := by dsimp [C, gaussianTailComparisonConstant]; linarith
  have hC : 0 < C := by linarith
  change μ.real {ω | t ≤ X ω} ≤ C * μ.real {ω | t / C ≤ Y ω}
  by_cases hsmall : t ≤ 2 * A * a
  · have hthresh : t / C ≤ a / 2 := by
      apply (div_le_iff₀ hC).mpr
      nlinarith [mul_le_mul_of_nonneg_right hCA ha.le]
    have hhalf := gaussianHalfMeanProbability_le_measure_ge_half_mean hm hκ hY hscale
    have hmono : μ.real {ω | a / 2 ≤ Y ω} ≤ μ.real {ω | t / C ≤ Y ω} :=
      measureReal_mono (fun ω hω => hthresh.trans hω) (by finiteness)
    have hprod : 1 ≤ C * gaussianHalfMeanProbability κ := by
      have hh := mul_le_mul_of_nonneg_right hCδ hδ.le
      rw [inv_mul_cancel₀ hδ.ne'] at hh
      exact hh
    exact measureReal_le_one.trans (hprod.trans
      (mul_le_mul_of_nonneg_left (hhalf.trans hmono) hC.le))
  · have hlarge : 2 * A * a ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have hcenter : t / 2 ≤ t - ∫ y, X y ∂μ := by dsimp [a] at hlarge; linarith
    have hmono : μ.real {ω | t ≤ X ω} ≤
        μ.real {ω | t / 2 ≤ X ω - ∫ y, X y ∂μ} :=
      measureReal_mono (fun ω hω => by dsimp at hω ⊢; linarith) (by finiteness)
    have hupper := hmono.trans (hX.measure_ge_le (show 0 ≤ t / 2 by positivity))
    have hexp : Real.exp (-(t / 2) ^ 2 / (2 * (2 * m ^ 2))) ≤
        Real.exp (-((t / C) / m) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hC2 : 16 ≤ C ^ 2 := by nlinarith
      rw [show -(t / 2) ^ 2 / (2 * (2 * m ^ 2)) = -(t ^ 2 / (16 * m ^ 2)) by ring,
        show -((t / C) / m) ^ 2 = -(t ^ 2 / (C ^ 2 * m ^ 2)) by ring]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg t)
        (by positivity) (mul_le_mul_of_nonneg_right hC2 (sq_nonneg m)))
    have hlow := hlower (t / C) (div_nonneg ht hC.le)
    have hprod : 1 ≤ C * c := by
      have hh := mul_le_mul_of_nonneg_right hCc hc.le
      rw [inv_mul_cancel₀ hc.ne'] at hh
      exact hh
    apply hupper.trans (hexp.trans ?_)
    have hh := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-((t / C) / m) ^ 2)).le
    have hh' : Real.exp (-((t / C) / m) ^ 2) ≤
        C * (c * Real.exp (-((t / C) / m) ^ 2)) := by
      simpa only [one_mul, mul_assoc] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hlow hC.le)

end NLAlib

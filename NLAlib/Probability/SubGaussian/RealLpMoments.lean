import NLAlib.Probability.SubGaussian.LpMoments
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Real-exponent moments of centered sub-Gaussian observables

Round the exponent up to an even integer, use the actual even Gaussian-type
moment bound, and compare probability-space norms. This gives square-root
growth for every real exponent at least two, including zero variance proxies.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace NLAlib

/-- A centered sub-Gaussian observable belongs to every finite `L^q`; the
uncentered mean is the actual Bochner integral. -/
theorem memLp_of_centered_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ) c μ) (q : ℝ≥0) :
    MemLp X q μ := by
  have hh := (h.memLp q).add (memLp_const (∫ y, X y ∂μ))
  have heq : ((fun ω => X ω - ∫ y, X y ∂μ) + fun _ => ∫ y, X y ∂μ) = X := by
    ext ω
    simp
  rwa [heq] at hh

/-- At every real exponent at least two, a nonnegative observable with
sub-Gaussian centered MGF has `L^p` norm at most its actual mean plus
`2 sqrt(c p)`. -/
theorem lpNorm_ofReal_le_integral_add_two_mul_sqrt_of_centered_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ) c μ)
    {p : ℝ} (hp : 2 ≤ p) :
    lpNorm X (ENNReal.ofReal p) μ ≤ (∫ ω, X ω ∂μ) + 2 * Real.sqrt ((c : ℝ) * p) := by
  let k := ⌈p / 2⌉₊
  have hp0 : 0 < p := by linarith
  have hk : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hlo : p ≤ 2 * (k : ℝ) := by
    have hh := Nat.le_ceil (p / 2)
    dsimp [k]
    linarith
  have hhi : (k : ℝ) ≤ p := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ p / 2)
    dsimp [k]
    linarith
  have hMq : MemLp X (2 * (k : ℝ≥0∞)) μ := by
    have hh := memLp_of_centered_hasSubgaussianMGF h (2 * (k : ℝ≥0))
    simpa using hh
  have hexp : ENNReal.ofReal p ≤ 2 * (k : ℝ≥0∞) := by
    calc
      _ ≤ ENNReal.ofReal (2 * (k : ℝ)) := ENNReal.ofReal_le_ofReal hlo
      _ = _ := by simp
  have hmono := ENNReal.toReal_mono hMq.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hexp hMq.aestronglyMeasurable)
  rw [toReal_eLpNorm hMq.aestronglyMeasurable,
    toReal_eLpNorm hMq.aestronglyMeasurable] at hmono
  apply (hmono.trans (lpNorm_le_integral_add_sqrt_of_centered_hasSubgaussianMGF hX h hk)).trans
  refine add_le_add le_rfl ?_
  calc
    Real.sqrt (4 * (c : ℝ) * k) ≤ Real.sqrt (4 * ((c : ℝ) * p)) :=
      Real.sqrt_le_sqrt (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi
          (show 0 ≤ 4 * (c : ℝ) from by positivity))
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

end NLAlib

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import NLAlib.ForMathlib.Analysis.Real

/-!
# Euclidean Lipschitz functions on `ι → ℝ`: continuity, gradient bound, smoothing

For `f : (ι → ℝ) → ℝ` with `|f x - f y| ≤ L √(∑ᵢ (xᵢ - yᵢ)²)` (Lipschitz for the Euclidean
distance, stated without `EuclideanSpace`):

* `continuous_of_abs_sub_le_mul_sqrt_sum_sq`: `f` is continuous;
* `sum_sq_fderiv_le_sq_of_lipschitz`: if `f` is differentiable, `∑ᵢ (∂ᵢ f)² ≤ L²`;
* `exists_contDiff_abs_sub_le_of_lipschitz`: `f` is uniformly approximated by `C^∞` functions
  that are again `L`-Lipschitz (mollification).

Candidates for `Mathlib/Analysis/Calculus/` and `Mathlib/Topology/EMetricSpace/Lipschitz`. Moved
from `NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration` (dedup round,
2026-10-12). Atlas: helpers of `gaussian-concentration`, `herbst`.
-/

noncomputable section

open MeasureTheory

namespace NLAlib

private lemma sqrt_sum_sq_sub_le_card_mul_dist {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Fintype.card ι * dist x y := by
  refine (sqrt_sum_sq_le_sum_abs (fun i => x i - y i)).trans ?_
  calc ∑ i, |x i - y i| ≤ ∑ _i : ι, dist x y := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
    _ = Fintype.card ι * dist x y := by simp

/-- A function that is `L`-Lipschitz for the Euclidean distance on `ι → ℝ` is continuous. Atlas:
`gaussian-concentration` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_lipschitz_entropy_bound`. -/
theorem continuous_of_abs_sub_le_mul_sqrt_sum_sq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) : Continuous f := by
  have h : ∀ x y, dist (f x) (f y) ≤ (L * Fintype.card ι) * dist x y := by
    intro x y
    rw [Real.dist_eq]
    refine (hLip x y).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL
    refine (sqrt_sum_sq_le_sum_abs (fun i => x i - y i)).trans ?_
    calc ∑ i, |x i - y i| ≤ ∑ _i : ι, dist x y := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
      _ = Fintype.card ι * dist x y := by simp
  exact (LipschitzWith.of_dist_le' h).continuous

/-- The gradient of a differentiable `L`-Lipschitz (Euclidean) function on `ι → ℝ` has squared norm
at most `L²`: `∑ᵢ (∂ᵢ g)² ≤ L²`. Atlas: `gaussian-concentration` (helper). Ported from Prove2me
solution `GaussianMatrix.gaussian_lipschitz_entropy_bound`. -/
theorem sum_sq_fderiv_le_sq_of_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : Differentiable ℝ g) (L : ℝ)
    (hLip : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (x : ι → ℝ) :
    ∑ i, (fderiv ℝ g x (Pi.single i 1)) ^ 2 ≤ L ^ 2 := by
  set D := fderiv ℝ g x with hD
  set v : ι → ℝ := fun i => D (Pi.single i 1) with hv
  set S := ∑ i, v i ^ 2 with hS
  have hDv : D v = S := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [this, map_smul, smul_eq_mul, sq]
  have hderiv : HasDerivAt (fun t : ℝ => g (x + t • v)) S 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt g D (x + (0:ℝ) • v) := by
      simpa using (hg x).hasFDerivAt
    rw [← hDv]
    exact h2.comp_hasDerivAt (x := (0:ℝ)) h1
  have ht := hderiv.tendsto_slope_zero_right
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hle : S ≤ L * Real.sqrt S := by
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
    have h := hLip (x + (0 + t) • v) (x + (0:ℝ) • v)
    have hsq : ∑ i, ((x + (0 + t) • v) i - (x + (0:ℝ) • v) i) ^ 2 = t ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp; ring
    rw [hsq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq htp.le] at h
    rw [smul_eq_mul]
    have h3 := (le_abs_self _).trans h
    rw [inv_mul_le_iff₀ htp]
    simp only [zero_add] at h3 ⊢
    linarith
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have hsp : 0 < Real.sqrt S := Real.sqrt_pos.mpr h0
    have hsL : Real.sqrt S ≤ L := by
      have : Real.sqrt S * Real.sqrt S ≤ L * Real.sqrt S := by
        rw [Real.mul_self_sqrt hS0]; exact hle
      exact le_of_mul_le_mul_right this hsp
    have : S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
    rw [this]
    exact pow_le_pow_left₀ hsp.le hsL 2

/-! ### Smooth approximation -/

/-- **Smooth approximation of Lipschitz functions**: an `L`-Lipschitz (Euclidean) function
`f : (ι → ℝ) → ℝ` is within `ε` of a `C^∞` function that is again `L`-Lipschitz (mollify with a
normed bump of small support). Source: standard; Ledoux, *Concentration of Measure*, §5.1.
Atlas: `gaussian-concentration` (helper). Ported from Prove2me solution
`GaussianMatrix.lipschitz_smooth_approx`. -/
theorem exists_contDiff_abs_sub_le_of_lipschitz {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (L : ℝ) (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ g : (ι → ℝ) → ℝ, (∀ n : ℕ, ContDiff ℝ n g) ∧
      (∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
      ∀ x, |g x - f x| ≤ ε := by
  set C : ℝ := |L| * Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have hdist : ∀ x y, dist (f x) (f y) ≤ C * dist x y := by
    intro x y
    rw [Real.dist_eq]
    refine (hLip x y).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _)).trans ?_
    rw [hC, mul_assoc]
    exact mul_le_mul_of_nonneg_left (sqrt_sum_sq_sub_le_card_mul_dist x y) (abs_nonneg L)
  have hcont : Continuous f := (LipschitzWith.of_dist_le' hdist).continuous
  set r : ℝ := ε / (C + 1) with hr
  have hr0 : 0 < r := div_pos hε (by linarith)
  have hCr : C * r ≤ ε := by
    rw [hr, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let φ : ContDiffBump (0 : ι → ℝ) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  set ψ : (ι → ℝ) → ℝ := φ.normed (volume : Measure (ι → ℝ)) with hψ
  set g : (ι → ℝ) → ℝ :=
    convolution ψ f (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (ι → ℝ)) with hg
  have hloc : LocallyIntegrable f (volume : Measure (ι → ℝ)) := hcont.locallyIntegrable
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hloc
  have hgdef : ∀ x, g x = ∫ t, ψ t * f (x - t) := by
    intro x
    rw [hg, convolution_lsmul]
    rfl
  have hint : ∀ x, Integrable (fun t => ψ t * f (x - t)) (volume : Measure (ι → ℝ)) := by
    intro x
    have := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc x
    exact this
  refine ⟨g, ?_, ?_, ?_⟩
  · intro n
    exact hsmooth.of_le (by exact_mod_cast le_top)
  · intro x y
    rw [hgdef x, hgdef y, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, |ψ t * f (x - t) - ψ t * f (y - t)|
        ≤ ψ t * (L * Real.sqrt (∑ i, (x i - y i) ^ 2)) := by
      intro t
      rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed (μ := volume) t)]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed (μ := volume) t)
      have := hLip (x - t) (y - t)
      simpa using this
    calc |∫ t, (ψ t * f (x - t) - ψ t * f (y - t))|
        ≤ ∫ t, |ψ t * f (x - t) - ψ t * f (y - t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t, ψ t * (L * Real.sqrt (∑ i, (x i - y i) ^ 2)) := by
          refine integral_mono ((hint x).sub (hint y)).abs ?_ hb
          exact (φ.integrable_normed (μ := volume)).mul_const _
      _ = L * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
          rw [integral_mul_const, φ.integral_normed (μ := volume), one_mul]
  · intro x
    rw [← Real.dist_eq]
    refine φ.dist_normed_convolution_le hcont.aestronglyMeasurable ?_
    intro y hy
    refine (hdist y x).trans ?_
    refine (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le hC0).trans ?_
    exact hCr

end NLAlib

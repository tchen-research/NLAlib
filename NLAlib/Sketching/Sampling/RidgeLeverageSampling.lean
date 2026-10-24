import NLAlib.Matrix.Functions.RidgeWhitening
import NLAlib.Sketching.Sampling.CovarianceBernstein

/-!
# Ridge leverage sampling under the actual finite row law

Upper bounds on the actual ridge leverage scores define normalized row probabilities.
Independent draws select and rescale the original data rows. Whitening identifies their
covariance with a contraction and yields the exact ambient-dimension Bernstein bound.
The stated sample count then gives a regularized Loewner approximation with failure at
most the prescribed probability.

Source: Cohen–Musco–Musco 2017, Theorem 5, ambient-dimension variant;
Tropp 2015, Theorem 6.1.1; `sketching_lowrank_routes_2026_10_24/sketching.tex`.
Atlas: `ridge-sampling-regularized-approximation`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Ridge-score upper bounds are nonnegative. -/
theorem nonneg_of_ridgeLeverageScore_le (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (u : m → ℝ) (hu : ∀ i, ridgeLeverageScore A ρ i ≤ u i) (i : m) : 0 ≤ u i :=
  (ridgeLeverageScore_nonneg A hρ i).trans (hu i)

/-- The exact whitening of the original sampled rows is the covariance difference
of the whitened rows. Thus whitening is used for analysis and does not change the sampler. -/
theorem sampled_ridgeWhitenedRows_gram_sub (A : Matrix m n ℝ) (ρ : ℝ)
    (p : m → ℝ≥0) {s : ℕ} (ω : Fin s → m) :
    (sampledRowMatrix (ridgeWhitenedRows A ρ) p ω)ᵀ *
        sampledRowMatrix (ridgeWhitenedRows A ρ) p ω -
        (ridgeWhitenedRows A ρ)ᵀ * ridgeWhitenedRows A ρ =
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ) *
        ((sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω - Aᵀ * A) *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ) := by
  let T := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ)
  have hT : T.IsHermitian := cfc_predicate _ _
  have hTs : Tᵀ = T := hT.eq
  change (sampledRowMatrix (A * T) p ω)ᵀ * sampledRowMatrix (A * T) p ω -
    (A * T)ᵀ * (A * T) = T * ((sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω - Aᵀ * A) * T
  rw [sampledRowMatrix_mul]
  simp only [Matrix.transpose_mul, hTs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Actual ridge-dominating row probabilities give the exact covariance Bernstein tail
for the literal sampled data matrix. Source: Cohen–Musco–Musco 2017, Theorem 5,
ambient-dimension variant; Tropp 2015, Theorem 6.1.1. -/
theorem measureReal_specNorm_ridge_sampled_gram_sub_le
    [MeasurableSpace m] [MeasurableSingletonClass m] [Nonempty n]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (p : m → ℝ≥0) (hp : ∑ i, p i = 1) {t : ℝ} (ht : 0 < t)
    (hdom : ∀ i, ridgeLeverageScore A ρ i ≤ t * (p i : ℝ))
    {s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw p hp)).real
      {ω | ε < specNorm (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ) *
        ((sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω - Aᵀ * A) *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ))} ≤
      2 * Fintype.card n * Real.exp (-(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3))) := by
  classical
  have hrow (i : m) : ∑ a, ‖ridgeWhitenedRows A ρ i a‖ ^ 2 = ridgeLeverageScore A ρ i := by
    calc
      _ = ridgeWhitenedRows A ρ i ⬝ᵥ ridgeWhitenedRows A ρ i := by
        unfold dotProduct
        apply Finset.sum_congr rfl
        intro a _
        rw [Real.norm_eq_abs, sq_abs, pow_two]
      _ = ‖(WithLp.toLp 2 (ridgeWhitenedRows A ρ i) : EuclideanSpace ℝ n)‖ ^ 2 :=
        (norm_toLp_sq_eq_dotProduct_self _).symm
      _ = _ := norm_ridgeWhitenedRows_row_sq A hρ i
  have h := measureReal_specNorm_sampled_transpose_mul_sub_le
    (ridgeWhitenedRows A ρ) p hp ht (transpose_ridgeWhitenedRows_mul_le_one A hρ)
    (fun i => (hrow i).le.trans (hdom i)) hs hε
  simpa only [sampled_ridgeWhitenedRows_gram_sub] using h

/-- Normalizing any upper bounds on the actual ridge scores gives the original
sampling theorem with `t` equal to their sum. This declaration specifies the complete
finite sampling law and the original, unwhitened sampled matrix.
Source: Cohen–Musco–Musco 2017, Theorem 5, ambient-dimension variant.
atlas: ridge-sampling-regularized-approximation (partial) -/
theorem measureReal_specNorm_ridge_sampled_gram_sub_le_of_upper_scores
    [MeasurableSpace m] [MeasurableSingletonClass m] [Nonempty n]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (u : m → ℝ) (hu : ∀ i, ridgeLeverageScore A ρ i ≤ u i) (ht : 0 < ∑ i, u i)
    {s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw (normalizedSamplingProbabilities u)
      (sum_normalizedSamplingProbabilities u (nonneg_of_ridgeLeverageScore_le A hρ u hu) ht))).real
      {ω | ε < specNorm (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ) *
        ((sampledRowMatrix A (normalizedSamplingProbabilities u) ω)ᵀ *
          sampledRowMatrix A (normalizedSamplingProbabilities u) ω - Aᵀ * A) *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ))} ≤
      2 * Fintype.card n * Real.exp (-(s : ℝ) * ε ^ 2 / (2 * (∑ i, u i) * (1 + ε / 3))) := by
  apply measureReal_specNorm_ridge_sampled_gram_sub_le A hρ _ _ ht _ hs hε
  intro i
  rw [normalizedSamplingProbabilities, Real.coe_toNNReal _
    (div_nonneg (nonneg_of_ridgeLeverageScore_le A hρ u hu i) ht.le)]
  simpa only [mul_div_cancel₀ _ ht.ne'] using hu i

/-- The exact Bernstein expression is at most `δ` at the explicit sufficient sample
count `3 t ε⁻² log(2 d / δ)`, for `0 < ε < 1`.
Source: Cohen–Musco–Musco 2017, Theorem 5, ambient-dimension variant. -/
theorem ridge_sampling_tail_le_of_sample_size {d s : ℕ} (hd : 0 < d)
    {t ε δ : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hsize : 3 * t / ε ^ 2 * Real.log (2 * d / δ) ≤ s) :
    2 * d * Real.exp (-(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3))) ≤ δ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (2 * d / δ) ≤ (s : ℝ) * ε ^ 2 / (3 * t) := by
    have h := mul_le_mul_of_nonneg_left hsize (show 0 ≤ ε ^ 2 / (3 * t) by positivity)
    have he : ε ^ 2 / (3 * t) * (3 * t / ε ^ 2 * Real.log (2 * d / δ)) =
        Real.log (2 * d / δ) := by field_simp
    rw [he] at h
    calc
      _ ≤ ε ^ 2 / (3 * t) * (s : ℝ) := h
      _ = _ := by ring
  have hsR : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hexp : -(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3)) ≤
      -Real.log (2 * d / δ) := by
    have hden : 0 < 2 * t * (1 + ε / 3) := by positivity
    have hdenle : 2 * t * (1 + ε / 3) ≤ 3 * t := by nlinarith
    have hq : (s : ℝ) * ε ^ 2 / (3 * t) ≤
        (s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3)) :=
      div_le_div_of_nonneg_left (by positivity) hden hdenle
    simpa only [neg_div, neg_mul] using neg_le_neg (hlog.trans hq)
  calc
    _ ≤ 2 * d * Real.exp (-Real.log (2 * d / δ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

/-- The literal row-sampling algorithm with upper ridge scores has failure probability
at most `δ` for the complete two-sided regularized Loewner approximation, at the stated
sample count. Repeated indices are retained as rows in the sampled list, and zero upper
scores are allowed. Source: Cohen–Musco–Musco 2017, Theorem 5, ambient-dimension variant.
atlas: ridge-sampling-regularized-approximation (partial) -/
theorem measureReal_ridge_sampling_failure_le_of_sample_size
    [MeasurableSpace m] [MeasurableSingletonClass m] [Nonempty n]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (u : m → ℝ) (hu : ∀ i, ridgeLeverageScore A ρ i ≤ u i) (ht : 0 < ∑ i, u i)
    {s : ℕ} (hs : 0 < s) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hsize : 3 * (∑ i, u i) / ε ^ 2 * Real.log (2 * Fintype.card n / δ) ≤ s) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw (normalizedSamplingProbabilities u)
      (sum_normalizedSamplingProbabilities u (nonneg_of_ridgeLeverageScore_le A hρ u hu) ht))).real
      {ω | ¬ ((1 - ε) • ridgeGram A ρ ≤
          ridgeGram (sampledRowMatrix A (normalizedSamplingProbabilities u) ω) ρ ∧
        ridgeGram (sampledRowMatrix A (normalizedSamplingProbabilities u) ω) ρ ≤
          (1 + ε) • ridgeGram A ρ)} ≤ δ := by
  apply le_trans (measureReal_mono ?_)
    ((measureReal_specNorm_ridge_sampled_gram_sub_le_of_upper_scores A hρ u hu ht hs hε).trans
      (ridge_sampling_tail_le_of_sample_size (Fintype.card_pos) ht hε hε1 hδ hsize))
  intro ω hω
  by_contra hnot
  exact hω (ridgeGram_bounds_of_specNorm_whitened_sub_le A
    (sampledRowMatrix A (normalizedSamplingProbabilities u) ω) hρ hε.le (not_lt.mp hnot))

end NLAlib

import NLAlib.Probability.Gaussian.Moments.SeriesHermiteBound
import NLAlib.Probability.Gaussian.Moments.SeriesNormMoments
import NLAlib.ForMathlib.Analysis.LogarithmicMomentOptimization

/-! # Expected Gaussian series norm from coefficient partial transpose

The actual finite Hermite moments are optimized over integer orders. Keeping
the exact `p - 1` factor gives correction constant four; the source constant
six and its `log(2d)` intermediate estimate follow. Dimension one and zero
correction scale are treated without excluding zero coefficient arrays.
Source: Bandeira et al. (2026), Theorem 1.5 and finite Hermite route.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

/-- Every positive integer moment bounds the actual expected Gaussian series
norm by the coefficient-sensitive finite Hermite expression. -/
theorem integral_specNorm_gaussianSeries_le_coefficientBlock_moment
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) {p : ℕ} (hp : 1 ≤ p) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      2 * (Fintype.card d : ℝ) ^ (1 / (2 * (p : ℝ))) *
        Real.sqrt (specNorm (coefficientVariance A) +
          ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) :=
  (integral_specNorm_gaussianSeries_le_even_trace_rpow A hA hp).trans
    (integral_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock A hA hp)

/-- The expected norm of an actual Hermitian Gaussian series has the exact
factor two leading term and correction constant four. This strengthens the
source constant six by retaining `p - 1` in the ceiling optimization.
Source: Bandeira et al. (2026), Theorem 1.5, finite Hermite route.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_partialTranspose_four
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        4 * coefficientBlockKappa A * Real.sqrt (Real.log (Fintype.card d)) := by
  have hmax := lambdaMax_coefficientBlock_nonneg A hA
  have hM : ∀ p : ℕ, 1 ≤ p →
      (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
        2 * (Fintype.card d : ℝ) ^ (1 / (2 * (p : ℝ))) *
          Real.sqrt ((Real.sqrt (specNorm (coefficientVariance A))) ^ 2 +
            ((p - 1 : ℕ) : ℝ) * coefficientBlockKappa A ^ 2) := by
    intro p hp
    simpa only [coefficientBlockKappa, Real.sq_sqrt hmax,
      Real.sq_sqrt (specNorm_nonneg _)] using
      integral_specNorm_gaussianSeries_le_coefficientBlock_moment A hA hp
  have hd : 1 ≤ Fintype.card d := Fintype.card_pos
  by_cases hd₁ : Fintype.card d = 1
  · have hh := hM 1 le_rfl
    simpa only [hd₁, Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero, add_zero,
      Real.one_rpow, Nat.sub_self, Nat.cast_zero, zero_mul, Real.sqrt_sq (Real.sqrt_nonneg _),
      mul_one] using hh
  · have hd₂ : (1 : ℝ) < Fintype.card d := by exact_mod_cast (show 1 < Fintype.card d by omega)
    exact Real.le_two_mul_add_four_mul_sqrt_log_of_even_moments
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hd₂ hM

/-- The source expected-norm bound with correction constant six holds for
all positive dimensions, including dimension one and zero coefficients.
Source: Bandeira et al. (2026), Theorem 1.5.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_partialTranspose
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        6 * coefficientBlockKappa A * Real.sqrt (Real.log (Fintype.card d)) := by
  apply (integral_specNorm_gaussianSeries_le_partialTranspose_four A hA).trans
  have hκ : 0 ≤ coefficientBlockKappa A := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.sqrt (Real.log (Fintype.card d)) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hκ hlog]

/-- The more precise `log(2d)` intermediate source estimate follows from
the exact finite-moment optimization, with correction constant four.
Source: Bandeira et al. (2026), Appendix A.2.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_partialTranspose_log_two
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        4 * coefficientBlockKappa A * Real.sqrt (Real.log (2 * (Fintype.card d : ℝ))) := by
  apply (integral_specNorm_gaussianSeries_le_partialTranspose_four A hA).trans
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hlog := Real.sqrt_le_sqrt (Real.log_le_log hd (show (Fintype.card d : ℝ) ≤ 2 * Fintype.card d by linarith))
  have hκ : 0 ≤ coefficientBlockKappa A := Real.sqrt_nonneg _
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hκ))

open scoped Matrix.Norms.L2Operator in
/-- The source coefficient-sensitive expected-norm theorem transported to a
random vector having the actual joint standard Gaussian law.
Source: Bandeira et al. (2026), Theorem 1.5.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_partialTranspose_of_hasLaw
    [Nonempty ι] [Nonempty d] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → ι → ℝ} (hξ : HasLaw ξ (gaussianVector ι) μ) :
    (∫ ω, specNorm (∑ i, ξ ω i • A i) ∂μ) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        6 * coefficientBlockKappa A * Real.sqrt (Real.log (Fintype.card d)) := by
  have hf : Continuous (fun x : ι → ℝ => specNorm (∑ i, x i • A i)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  rw [show (∫ ω, specNorm (∑ i, ξ ω i • A i) ∂μ) =
      ∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_specNorm_gaussianSeries_le_partialTranspose A hA

end NLAlib

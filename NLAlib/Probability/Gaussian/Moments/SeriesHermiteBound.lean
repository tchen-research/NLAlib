import NLAlib.Probability.Gaussian.Moments.SeriesHermiteVacuum
import NLAlib.Matrix.Structured.HermiteNorm
import NLAlib.Matrix.Functions.PolynomialSeries

/-! # Gaussian trace moments with the coefficient-block parameter

The finite cutoff `p`, its exact Gaussian vacuum identity, and its sharp
deterministic norm bound prove the strengthened Gaussian even-moment theorem.
Both normalized and unnormalized trace conventions are exposed, together with
transport to arbitrary probability spaces through the joint Gaussian law.
Source: Bandeira et al. (2026), Theorem 1.5 and finite Hermite route.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_pow_le (H : Matrix d d ℂ) (p : ℕ) : specNorm (H ^ p) ≤ specNorm H ^ p := by
  cases isEmpty_or_nonempty d with
  | inl hd =>
    have hz : H ^ p = 0 := Subsingleton.elim _ _
    rw [hz, specNorm_zero]
    exact pow_nonneg (specNorm_nonneg _) _
  | inr hd => simpa only [specNorm_eq_norm] using norm_pow_le H p

/-- The actual unnormalized Gaussian even trace moment is bounded by the
dimension times the sharp coefficient-sensitive finite cutoff norm power.
Source: Bandeira et al. (2026), Theorem 2.1, finite Hermite route.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_re_trace_gaussianSeries_even_pow_le_coefficientBlock
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) ≤
      (Fintype.card d : ℝ) *
        (2 * Real.sqrt (specNorm (coefficientVariance A) +
          ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A))) ^ (2 * p) := by
  let H := hermiteSeriesOperator A p
  let C := 2 * Real.sqrt (specNorm (coefficientVariance A) +
    ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A))
  have hC : specNorm H ≤ C := specNorm_hermiteSeriesCreation_add_conjTranspose_le A hA p
  have hCp : specNorm (H ^ p) ≤ C ^ p :=
    (specNorm_pow_le H p).trans (pow_le_pow_left₀ (specNorm_nonneg _) hC p)
  rw [integral_re_trace_gaussianSeries_even_pow_eq_frobSq_hermiteVacuum A hA]
  calc
    _ ≤ specNorm (H ^ p) ^ 2 * frobSq (hermiteVacuumEmbedding d ι p) :=
      frobSq_mul_le_specNorm_sq_mul_frobSq _ _
    _ ≤ (C ^ p) ^ 2 * (Fintype.card d : ℝ) := by
      rw [frobSq_hermiteVacuumEmbedding]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (specNorm_nonneg _) hCp 2)
        (Nat.cast_nonneg _)
    _ = _ := by rw [← pow_mul, mul_comm p 2, mul_comm]

/-- The unnormalized rooted Gaussian trace moment includes exactly the
dimension factor `d^(1/(2p))`.
Source: Bandeira et al. (2026), Theorem 1.5; source normalized trace converted.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) {p : ℕ} (hp : 1 ≤ p) :
    (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) ^ (1 / (2 * (p : ℝ))) ≤
      2 * (Fintype.card d : ℝ) ^ (1 / (2 * (p : ℝ))) *
        Real.sqrt (specNorm (coefficientVariance A) +
          ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) := by
  let C := 2 * Real.sqrt (specNorm (coefficientVariance A) +
    ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A))
  have hC : 0 ≤ C := by positivity
  have hM := integral_re_trace_gaussianSeries_even_pow_le_coefficientBlock A hA p
  have hn : 0 ≤ ∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι :=
    integral_nonneg fun x => re_trace_pow_nonneg_of_even _
      (isHermitian_sum_smul_real A hA x) (even_two_mul p)
  have hh := Real.rpow_le_rpow hn hM (show 0 ≤ 1 / (2 * (p : ℝ)) by positivity)
  change _ ≤ ((Fintype.card d : ℝ) * C ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) at hh
  have he : 1 / (2 * (p : ℝ)) = (((2 * p : ℕ) : ℝ))⁻¹ := by simp
  rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hC _), he,
    Real.pow_rpow_inv_natCast hC (by omega : 2 * p ≠ 0)] at hh
  change _ ≤ _ * C at hh
  simpa only [C, he, mul_assoc, mul_left_comm] using hh

/-- The normalized Gaussian even trace moment has the exact factor-two
finite Hermite bound, including singular and all-zero coefficient arrays.
Source: Bandeira et al. (2026), Theorem 1.5, normalized trace convention.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_normalized_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock
    [Nonempty ι] [Nonempty d] (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) {p : ℕ} (hp : 1 ≤ p) :
    ((∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) /
      (Fintype.card d : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A) +
        ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) := by
  let C := 2 * Real.sqrt (specNorm (coefficientVariance A) +
    ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A))
  have hC : 0 ≤ C := by positivity
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hM := integral_re_trace_gaussianSeries_even_pow_le_coefficientBlock A hA p
  have hdiv : (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) /
      (Fintype.card d : ℝ) ≤ C ^ (2 * p) := by
    exact (div_le_iff₀ hd).mpr (hM.trans_eq (mul_comm _ _))
  have hn : 0 ≤ (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) /
      (Fintype.card d : ℝ) := div_nonneg
    (integral_nonneg fun x => re_trace_pow_nonneg_of_even _
      (isHermitian_sum_smul_real A hA x) (even_two_mul p)) hd.le
  have hh := Real.rpow_le_rpow hn hdiv (show 0 ≤ 1 / (2 * (p : ℝ)) by positivity)
  have he : 1 / (2 * (p : ℝ)) = (((2 * p : ℕ) : ℝ))⁻¹ := by simp
  rw [he, Real.pow_rpow_inv_natCast hC (by omega : 2 * p ≠ 0)] at hh
  simpa only [← he, C] using hh

open scoped Matrix.Norms.L2Operator in
private theorem integral_trace_pow_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ι → Matrix d d ℂ) {ξ : Ω → ι → ℝ}
    (hξ : HasLaw ξ (gaussianVector ι) μ) (k : ℕ) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ k).trace.re ∂μ) =
      ∫ x, ((∑ i, x i • A i) ^ k).trace.re ∂gaussianVector ι := by
  have hf : Continuous (fun x : ι → ℝ => ((∑ i, x i • A i) ^ k).trace.re) := by
    fun_prop
  exact hξ.integral_comp hf.aestronglyMeasurable

/-- The unnormalized rooted moment bound applies to any random coefficient
vector with the actual joint standard Gaussian law.
Source: Bandeira et al. (2026), Theorem 1.5, unnormalized trace conversion.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock_of_hasLaw
    [Nonempty ι] [Nonempty d] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → ι → ℝ} (hξ : HasLaw ξ (gaussianVector ι) μ) {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) ^ (1 / (2 * (p : ℝ))) ≤
      2 * (Fintype.card d : ℝ) ^ (1 / (2 * (p : ℝ))) *
        Real.sqrt (specNorm (coefficientVariance A) +
          ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) := by
  rw [integral_trace_pow_of_hasLaw A hξ]
  exact integral_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock A hA hp

/-- The normalized rooted moment theorem on an arbitrary probability space,
with joint Gaussian law and the exact finite cutoff coefficient correction.
Source: Bandeira et al. (2026), Theorem 1.5.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_normalized_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock_of_hasLaw
    [Nonempty ι] [Nonempty d] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → ι → ℝ} (hξ : HasLaw ξ (gaussianVector ι) μ) {p : ℕ} (hp : 1 ≤ p) :
    ((∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) /
      (Fintype.card d : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A) +
        ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) := by
  rw [integral_trace_pow_of_hasLaw A hξ]
  exact integral_normalized_re_trace_gaussianSeries_even_pow_rpow_le_coefficientBlock A hA hp

end NLAlib

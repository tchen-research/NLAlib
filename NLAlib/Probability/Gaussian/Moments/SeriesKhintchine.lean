import NLAlib.Probability.Gaussian.Moments.Khintchine
import NLAlib.Probability.Concentration.Matrix.RademacherKhintchine

/-!
# Noncommutative Khintchine on arbitrary probability spaces

Transport the Gaussian and Rademacher trace-moment bounds through their joint laws.
Source: Tropp 2015, *An Introduction to Matrix Concentration Inequalities*, §4.7.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ComplexOrder
namespace NLAlib

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} {n : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- The noncommutative Khintchine bound for a vector with Gaussian law.
Source: Tropp 2015, §4.7.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_gaussianSeries_pow_le_of_hasLaw
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → Fin n → ℝ} (hξ : HasLaw ξ (gaussianVector (Fin n)) μ)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) ≤
      (2 * p - 1 : ℕ) ^ p * ((∑ i, A i ^ 2) ^ p).trace.re := by
  have hf : Continuous (fun x : Fin n → ℝ => ((∑ i, x i • A i) ^ (2 * p)).trace.re) := by
    simpa only [one_mul, pow_zero, mul_one] using
      continuous_re_trace_series_product A 1 1 (2 * p) 0
  rw [show (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) =
      ∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂(gaussianVector (Fin n)) from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_re_trace_gaussianSeries_pow_le A hA hp

open scoped Matrix.Norms.L2Operator in
/-- The rooted noncommutative Khintchine bound for a vector with Gaussian law.
Source: Tropp 2015, §4.7.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_gaussianSeries_pow_rpow_le_of_hasLaw
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → Fin n → ℝ} (hξ : HasLaw ξ (gaussianVector (Fin n)) μ)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt (2 * p - 1 : ℕ) *
        (((∑ i, A i ^ 2) ^ p).trace.re) ^ (1 / (2 * (p : ℝ))) := by
  apply rpow_le_sqrt_mul_rpow_of_nat_pow_le
  · exact integral_nonneg fun ω => re_trace_pow_nonneg_of_even _
      (isHermitian_sum_smul_real A hA (ξ ω)) (even_two_mul p)
  · exact re_trace_pow_nonneg_of_posSemidef _ (posSemidef_sum_sq_of_isHermitian A hA) p
  · exact Nat.cast_nonneg _
  · exact hp
  · exact integral_re_trace_gaussianSeries_pow_le_of_hasLaw A hA hξ hp

open scoped Matrix.Norms.L2Operator in
/-- The noncommutative Khintchine bound for a vector with Rademacher law.
Source: Tropp 2015, §4.7.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_rademacherSeries_pow_le_of_hasLaw
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → κ → ℝ} (hξ : HasLaw ξ (rademacherVector (κ)) μ)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) ≤
      (2 * p - 1 : ℕ) ^ p * ((∑ i, A i ^ 2) ^ p).trace.re := by
  have hf : Continuous (fun x : κ → ℝ => ((∑ i, x i • A i) ^ (2 * p)).trace.re) := by
    simpa only [one_mul, pow_zero, mul_one] using
      continuous_re_trace_series_product A 1 1 (2 * p) 0
  rw [show (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) =
      ∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂(rademacherVector (κ)) from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_re_trace_rademacherSeries_pow_le A hA hp

open scoped Matrix.Norms.L2Operator in
/-- The rooted noncommutative Khintchine bound for a vector with Rademacher law.
Source: Tropp 2015, §4.7.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_rademacherSeries_pow_rpow_le_of_hasLaw
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ξ : Ω → κ → ℝ} (hξ : HasLaw ξ (rademacherVector (κ)) μ)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ (2 * p)).trace.re ∂μ) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt (2 * p - 1 : ℕ) *
        (((∑ i, A i ^ 2) ^ p).trace.re) ^ (1 / (2 * (p : ℝ))) := by
  apply rpow_le_sqrt_mul_rpow_of_nat_pow_le
  · exact integral_nonneg fun ω => re_trace_pow_nonneg_of_even _
      (isHermitian_sum_smul_real A hA (ξ ω)) (even_two_mul p)
  · exact re_trace_pow_nonneg_of_posSemidef _ (posSemidef_sum_sq_of_isHermitian A hA) p
  · exact Nat.cast_nonneg _
  · exact hp
  · exact integral_re_trace_rademacherSeries_pow_le_of_hasLaw A hA hξ hp

end NLAlib

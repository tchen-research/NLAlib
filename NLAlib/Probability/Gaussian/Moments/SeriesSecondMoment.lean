import NLAlib.Probability.Gaussian.Moments.SeriesKhintchine
/-!
# Exact second moment of Gaussian and Rademacher matrix series

The order-one endpoint of noncommutative Khintchine is equality, not merely
an upper bound. Both coefficient laws yield the exact variance trace.
Source: Tropp 2015, *An Introduction to Matrix Concentration Inequalities*, §4.7.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ComplexOrder
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- The standard Gaussian matrix series has exact second trace moment
equal to the sum of coefficient square traces. Hermiticity is unnecessary
for this identity. Source: coordinate Stein at exponent one; Tropp 2015, §4.7. -/
theorem integral_re_trace_gaussianSeries_sq
    (A : Fin n → Matrix ι ι ℂ) :
    (∫ x : Fin n → ℝ, ((∑ i, x i • A i) ^ 2).trace.re
        ∂(gaussianVector _)) = (∑ i, A i ^ 2).trace.re := by
  have hpoint (x : Fin n → ℝ) : ((∑ i, x i • A i) ^ 2).trace.re =
      ∑ i, x i * (A i * (∑ j, x j • A j) ^ 1).trace.re := by
    rw [pow_two, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, pow_one]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun i _ =>
    integrable_coordinate_mul_re_trace_mul_gaussianSeries_pow A (A i) 1 i]
  simp_rw [integral_coordinate_mul_re_trace_mul_gaussianSeries_pow]
  simp only [Finset.sum_range_one, show Nat.pred 1 = 0 by rfl, Nat.sub_zero, pow_zero, mul_one]
  simp only [integral_const, probReal_univ, one_smul, Matrix.trace_sum, Complex.re_sum, pow_two]

open scoped Matrix.Norms.L2Operator in
/-- The finite product Rademacher matrix series has exact second
trace moment equal to the sum of coefficient square traces. Source: two-coordinate sign moments; Tropp 2015, §4.7. Hermiticity is unnecessary for the identity. -/
theorem integral_re_trace_rademacherSeries_sq
    {κ : Type*} [Fintype κ] [DecidableEq κ] (A : κ → Matrix ι ι ℂ) :
    (∫ x : κ → ℝ, ((∑ i, x i • A i) ^ 2).trace.re
        ∂(rademacherVector _)) = (∑ i, A i ^ 2).trace.re := by
  have hpoint (x : κ → ℝ) : ((∑ i, x i • A i) ^ 2).trace.re =
      ∑ i, x i * (A i * (∑ j, x j • A j) ^ 1).trace.re := by
    rw [pow_two, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, pow_one]
  have hcoord (i : κ) :
      (∫ x : κ → ℝ, x i * (A i * (∑ j, x j • A j) ^ 1).trace.re
          ∂(rademacherVector _)) = (A i ^ 2).trace.re := by
    have he (x : κ → ℝ) : x i * (A i * (∑ j, x j • A j) ^ 1).trace.re =
        ∑ j, (x i * x j) * (A i * A j).trace.re := by
      rw [pow_one, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      ring
    simp_rw [he]
    rw [integral_finsetSum _ fun j _ =>
      (integrable_coordinate_mul_coordinate_rademacherVector i j).mul_const _]
    simp_rw [integral_mul_const, integral_coordinate_mul_coordinate_rademacherVector]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun i _ =>
    integrable_coordinate_mul_re_trace_mul_rademacherSeries_pow A (A i) 1 i]
  simp_rw [hcoord]
  rw [Matrix.trace_sum, Complex.re_sum]

open scoped Matrix.Norms.L2Operator in
/-- Independent centred unit-variance coefficients have second trace moment
`re tr(∑ Aᵢ²)`. Hermiticity is unnecessary.
Source: Tropp 2015, §4.7, the second-moment identity.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_independent_series_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (A : κ → Matrix ι ι ℂ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (h2 : ∀ i, MemLp (ξ i) 2 μ)
    (h0 : ∀ i, ∫ ω, ξ i ω ∂μ = 0) (h1 : ∀ i, ∫ ω, ξ i ω ^ 2 ∂μ = 1) :
    (∫ ω, ((∑ i, ξ i ω • A i) ^ 2).trace.re ∂μ) = (∑ i, A i ^ 2).trace.re := by
  have hexp (ω) : ((∑ i, ξ i ω • A i) ^ 2).trace.re =
      ∑ i, ∑ j, (ξ i ω * ξ j ω) * (A i * A j).trace.re := by
    simp [sq, Finset.sum_mul_sum, Matrix.trace_sum, Matrix.trace_smul,
      Complex.re_sum, mul_left_comm, mul_assoc]
  have hint (i j) : Integrable (fun ω => ξ i ω * ξ j ω) μ :=
    (h2 i).integrable_mul (h2 j)
  have hcorr (i j) : ∫ ω, ξ i ω * ξ j ω ∂μ = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst hij
      simpa [sq] using h1 i
    · rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
        (hξ i).aestronglyMeasurable (hξ j).aestronglyMeasurable, h0 i, zero_mul]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hint i j).mul_const _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).mul_const _),
    integral_mul_const, hcorr]
  simp [Matrix.trace_sum, Complex.re_sum, sq]

open scoped Matrix.Norms.L2Operator in
/-- The exact second trace moment transported through a Gaussian vector law. -/
theorem integral_re_trace_gaussianSeries_sq_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Fin n → Matrix ι ι ℂ)
    {ξ : Ω → Fin n → ℝ} (hξ : HasLaw ξ (gaussianVector (Fin n)) μ) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ 2).trace.re ∂μ) = (∑ i, A i ^ 2).trace.re := by
  have hf : Continuous (fun x : Fin n → ℝ => ((∑ i, x i • A i) ^ 2).trace.re) := by
    simpa only [one_mul, pow_zero, mul_one] using continuous_re_trace_series_product A 1 1 2 0
  rw [show (∫ ω, ((∑ i, ξ ω i • A i) ^ 2).trace.re ∂μ) =
      ∫ x, ((∑ i, x i • A i) ^ 2).trace.re ∂(gaussianVector (Fin n)) from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_re_trace_gaussianSeries_sq A

open scoped Matrix.Norms.L2Operator in
/-- The exact second trace moment transported through a Rademacher vector law. -/
theorem integral_re_trace_rademacherSeries_sq_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Matrix ι ι ℂ)
    {ξ : Ω → κ → ℝ} (hξ : HasLaw ξ (rademacherVector (κ)) μ) :
    (∫ ω, ((∑ i, ξ ω i • A i) ^ 2).trace.re ∂μ) = (∑ i, A i ^ 2).trace.re := by
  have hf : Continuous (fun x : κ → ℝ => ((∑ i, x i • A i) ^ 2).trace.re) := by
    simpa only [one_mul, pow_zero, mul_one] using continuous_re_trace_series_product A 1 1 2 0
  rw [show (∫ ω, ((∑ i, ξ ω i • A i) ^ 2).trace.re ∂μ) =
      ∫ x, ((∑ i, x i • A i) ^ 2).trace.re ∂(rademacherVector (κ)) from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_re_trace_rademacherSeries_sq A

end NLAlib

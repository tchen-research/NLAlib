import NLAlib.Gaussian.SeriesKhintchine

/-!
# Exact second moment of Gaussian and Rademacher matrix series

The order-one endpoint of noncommutative Khintchine is equality, not merely
an upper bound. Both coefficient laws yield the exact variance trace.
Source: operator manuscript, endpoint following `thm:khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The actual standard Gaussian matrix series has exact second trace moment
equal to the sum of coefficient square traces. Hermiticity is unnecessary
for this identity. Source: coordinate Stein at exponent one; the order-one
endpoint of manuscript `thm:khintchine`. -/
theorem integral_re_trace_gaussianSeries_sq
    (A : Fin n → Matrix ι ι ℂ) :
    (∫ x : Fin n → ℝ, ((∑ i, x i • A i) ^ 2).trace.re
        ∂Measure.pi (fun _ => gaussianReal 0 1)) = (∑ i, A i ^ 2).trace.re := by
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

/-- The actual finite product Rademacher matrix series has exact second
trace moment equal to the sum of coefficient square traces. Source: actual
two-coordinate sign moments; the order-one endpoint of manuscript
`thm:khintchine`. Hermiticity is unnecessary for the identity. -/
theorem integral_re_trace_rademacherSeries_sq
    {κ : Type*} [Fintype κ] [DecidableEq κ] (A : κ → Matrix ι ι ℂ) :
    (∫ x : κ → ℝ, ((∑ i, x i • A i) ^ 2).trace.re
        ∂Measure.pi (fun _ => rademacherMeasure)) = (∑ i, A i ^ 2).trace.re := by
  have hpoint (x : κ → ℝ) : ((∑ i, x i • A i) ^ 2).trace.re =
      ∑ i, x i * (A i * (∑ j, x j • A j) ^ 1).trace.re := by
    rw [pow_two, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, pow_one]
  have hcoord (i : κ) :
      (∫ x : κ → ℝ, x i * (A i * (∑ j, x j • A j) ^ 1).trace.re
          ∂Measure.pi (fun _ => rademacherMeasure)) = (A i ^ 2).trace.re := by
    have he (x : κ → ℝ) : x i * (A i * (∑ j, x j • A j) ^ 1).trace.re =
        ∑ j, (x i * x j) * (A i * A j).trace.re := by
      rw [pow_one, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      ring
    simp_rw [he]
    rw [integral_finsetSum _ fun j _ =>
      (integrable_coordinate_mul_coordinate_pi_rademacherMeasure i j).mul_const _]
    simp_rw [integral_mul_const, integral_coordinate_mul_coordinate_pi_rademacherMeasure]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun i _ =>
    integrable_coordinate_mul_re_trace_mul_rademacherSeries_pow A (A i) 1 i]
  simp_rw [hcoord]
  rw [Matrix.trace_sum, Complex.re_sum]

/-- **Exact order-one endpoint.** Independent actual Gaussian or Rademacher
coefficients on any probability space have second trace moment exactly
`re tr(∑ Aᵢ²)`. Source: endpoint following manuscript `thm:khintchine`.
It includes empty matrices and coefficient families; no moment assumptions
or integrability hypotheses are added.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_independent_series_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Fin n → Matrix ι ι ℂ)
    (ξ : Fin n → Ω → ℝ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hlaw : (∀ i, IsStandardGaussian μ (ξ i)) ∨ (∀ i, IsRademacher μ (ξ i))) :
    (∫ ω, ((∑ i, ξ i ω • A i) ^ 2).trace.re ∂μ) = (∑ i, A i ^ 2).trace.re := by
  let X := fun ω i => ξ i ω
  let f := fun x : Fin n → ℝ => ((∑ i, x i • A i) ^ 2).trace.re
  have hX : Measurable X := measurable_pi_lambda _ hξ
  have hf : Continuous f := by
    simpa only [one_mul, pow_zero, mul_one] using continuous_re_trace_series_product A 1 1 2 0
  have hjoint := hind.map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)
  have hm : (∫ x, f x ∂μ.map X) = ∫ ω, f (X ω) ∂μ :=
    integral_map hX.aemeasurable hf.aestronglyMeasurable
  rcases hlaw with hlaw | hlaw
  · have hprod : μ.map X = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      rw [hjoint]
      exact congrArg Measure.pi (funext fun i => hlaw i)
    rw [hprod] at hm
    rw [← hm]
    exact integral_re_trace_gaussianSeries_sq A
  · have hprod : μ.map X = Measure.pi (fun _ : Fin n => rademacherMeasure) := by
      rw [hjoint]
      exact congrArg Measure.pi (funext fun i => hlaw i)
    rw [hprod] at hm
    rw [← hm]
    exact integral_re_trace_rademacherSeries_sq A

end NLAlib

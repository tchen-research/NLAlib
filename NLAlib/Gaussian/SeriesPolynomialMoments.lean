import NLAlib.Gaussian.PolynomialLinearMoments
import NLAlib.Matrix.PolynomialSeries

/-!
# Absolute moments and Stein identities of Gaussian matrix series

All trace polynomials, their coordinate products and derivatives are genuinely
integrable under the finite standard Gaussian law. The coordinate Stein
identity is applied only after these hypotheses have been proved.
Source: operator manuscript, Gaussian branch of `noncommutative-khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Every polynomial trace product of a finite Gaussian matrix series is
absolutely integrable. Source: polynomial growth and Gaussian moments;
supports `noncommutative-khintchine`. -/
theorem integrable_re_trace_gaussianSeries_product
    (A : Fin n → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) :
    Integrable (fun x : Fin n → ℝ =>
      (B * (∑ i, x i • A i) ^ r * C * (∑ i, x i • A i) ^ s).trace.re)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  apply integrable_pi_gaussianReal_of_polynomial_growth
    (continuous_re_trace_series_product A B C r s).measurable.aemeasurable _ (r + s)
  exact abs_re_trace_series_product_le A B C r s

/-- A coordinate times a Gaussian-series polynomial trace is absolutely
integrable. Source: polynomial growth and Gaussian absolute moments;
supports the coordinate Stein step for `noncommutative-khintchine`. -/
theorem integrable_coordinate_mul_re_trace_gaussianSeries_product
    (A : Fin n → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i *
      (B * (∑ j, x j • A j) ^ r * C * (∑ j, x j • A j) ^ s).trace.re)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  let D := ‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ * ‖B‖ * ‖C‖ *
    (∑ j, ‖A j‖) ^ (r + s)
  apply integrable_pi_gaussianReal_of_polynomial_growth
    ((continuous_apply i).mul (continuous_re_trace_series_product A B C r s)).measurable.aemeasurable
    D (r + s + 1)
  intro x
  have hi : |x i| ≤ 1 + ‖x‖ := by
    have h := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h
    linarith
  simp only [Pi.mul_apply]
  rw [abs_mul, pow_succ]
  calc _ ≤ (1 + ‖x‖) * (D * (1 + ‖x‖) ^ (r + s)) :=
      mul_le_mul hi (abs_re_trace_series_product_le A B C r s x)
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- A single matrix-series power inside real trace is absolutely integrable.
Source: the preceding polynomial-growth theorem; supports
`noncommutative-khintchine`. -/
theorem integrable_re_trace_mul_gaussianSeries_pow
    (A : Fin n → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (q : ℕ) :
    Integrable (fun x : Fin n → ℝ => (B * (∑ i, x i • A i) ^ q).trace.re)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  simpa only [pow_zero, mul_one] using
    integrable_re_trace_gaussianSeries_product A B 1 q 0

/-- A Gaussian coordinate times a one-power trace is absolutely integrable.
Source: polynomial Gaussian moments; supports `noncommutative-khintchine`. -/
theorem integrable_coordinate_mul_re_trace_mul_gaussianSeries_pow
    (A : Fin n → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (q : ℕ) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i * (B * (∑ j, x j • A j) ^ q).trace.re)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  simpa only [pow_zero, mul_one] using
    integrable_coordinate_mul_re_trace_gaussianSeries_product A B 1 q 0 i

/-- Coordinate Stein for complex matrix-series powers. The derivative uses
the genuine noncommutative product rule and all integrability is discharged.
Source: manuscript Gaussian `eq:recursion`; supports
`noncommutative-khintchine`. -/
theorem integral_coordinate_mul_re_trace_mul_gaussianSeries_pow
    (A : Fin n → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (q : ℕ) (i : Fin n) :
    (∫ x : Fin n → ℝ, x i * (B * (∑ j, x j • A j) ^ q).trace.re
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∑ l ∈ Finset.range q,
        ∫ x : Fin n → ℝ,
          (B * (∑ j, x j • A j) ^ (q.pred - l) *
            A i * (∑ j, x j • A j) ^ l).trace.re
          ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let f := fun x : Fin n → ℝ => (B * (∑ j, x j • A j) ^ q).trace.re
  let df := fun x : Fin n → ℝ => ∑ l ∈ Finset.range q,
    (B * (∑ j, x j • A j) ^ (q.pred - l) * A i * (∑ j, x j • A j) ^ l).trace.re
  have hdi : Integrable df (Measure.pi fun _ => gaussianReal 0 1) := by
    apply integrable_finsetSum
    intro l _
    exact integrable_re_trace_gaussianSeries_product A B (A i) (q.pred - l) l
  have hs := integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update f df i
    (fun x t => hasDerivAt_re_trace_mul_series_pow_update A B x i t q)
    (integrable_re_trace_mul_gaussianSeries_pow A B q)
    (integrable_coordinate_mul_re_trace_mul_gaussianSeries_pow A B q i) hdi
  rw [hs]
  exact integral_finsetSum _ fun l _ =>
    integrable_re_trace_gaussianSeries_product A B (A i) (q.pred - l) l

end NLAlib

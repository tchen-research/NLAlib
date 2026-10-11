import NLAlib.Concentration.Scalar.RademacherSymmetry
import NLAlib.Matrix.PolynomialSeries

/-!
# Polynomial moments under the finite Rademacher law

Absolute integrability of matrix-series trace polynomials and their coordinate
products follows from the actual two-atom product law, without additional
moment or integrability assumptions.
Source: operator manuscript, Rademacher branch of `noncommutative-khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open MeasureTheory Matrix
namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Every trace product of a finite Rademacher matrix series is absolutely
integrable under its actual product law. Source: bounded sign support;
supports `noncommutative-khintchine`. -/
theorem integrable_re_trace_rademacherSeries_product
    (A : κ → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) :
    Integrable (fun x : κ → ℝ =>
      (B * (∑ i, x i • A i) ^ r * C * (∑ i, x i • A i) ^ s).trace.re)
      (Measure.pi fun _ => rademacherMeasure) := by
  apply integrable_pi_rademacherMeasure_of_polynomial_growth _
    (continuous_re_trace_series_product A B C r s).measurable _ (r + s)
  exact abs_re_trace_series_product_le A B C r s

/-- A coordinate times a Rademacher-series trace polynomial is integrable
under its actual product law. Source: bounded sign support;
supports the sign-flip argument for `noncommutative-khintchine`. -/
theorem integrable_coordinate_mul_re_trace_rademacherSeries_product
    (A : κ → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) (i : κ) :
    Integrable (fun x : κ → ℝ => x i *
      (B * (∑ j, x j • A j) ^ r * C * (∑ j, x j • A j) ^ s).trace.re)
      (Measure.pi fun _ => rademacherMeasure) := by
  let D := ‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ * ‖B‖ * ‖C‖ *
    (∑ j, ‖A j‖) ^ (r + s)
  apply integrable_pi_rademacherMeasure_of_polynomial_growth _
    ((continuous_apply i).mul (continuous_re_trace_series_product A B C r s)).measurable
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

/-- A constant matrix times one Rademacher-series power has integrable real
trace. Source: bounded sign support; supports `noncommutative-khintchine`. -/
theorem integrable_re_trace_mul_rademacherSeries_pow
    (A : κ → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (q : ℕ) :
    Integrable (fun x : κ → ℝ => (B * (∑ i, x i • A i) ^ q).trace.re)
      (Measure.pi fun _ => rademacherMeasure) := by
  simpa only [pow_zero, mul_one] using integrable_re_trace_rademacherSeries_product A B 1 q 0

/-- A signed coefficient times a one-power trace is integrable under the
actual product Rademacher law. Source: bounded sign support; supports
`noncommutative-khintchine`. -/
theorem integrable_coordinate_mul_re_trace_mul_rademacherSeries_pow
    (A : κ → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (q : ℕ) (i : κ) :
    Integrable (fun x : κ → ℝ => x i * (B * (∑ j, x j • A j) ^ q).trace.re)
      (Measure.pi fun _ => rademacherMeasure) := by
  simpa only [pow_zero, mul_one] using
    integrable_coordinate_mul_re_trace_rademacherSeries_product A B 1 q 0 i

end NLAlib

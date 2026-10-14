import NLAlib.Polynomial.Quadrature.MeasureExactness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Clearing a fixed denominator in quadrature

The native positive measure with reciprocal polynomial density turns rational
exactness into ordinary polynomial exactness. Positivity of the denominator on
the measure is explicit; nonvanishing alone would not justify a positive measure.
Source: Gautschi (2004), rational Gauss rules; operator derivations AQ36.
-/

noncomputable section

open Polynomial MeasureTheory Set Finset

namespace NLAlib

/-- A positive measure with reciprocal polynomial density. On points where the
polynomial is positive this is exactly `dμ/ω`; elsewhere the real density is
truncated at zero by `ENNReal.ofReal`. Rational identities assume positivity
almost everywhere and therefore do not use the truncation convention. -/
def dividedPolynomialMeasure (μ : Measure ℝ) (ω : ℝ[X]) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal ((ω.eval x)⁻¹))

/-- Integration against the reciprocal-density measure is division by the
polynomial inside the actual original integral. -/
theorem integral_dividedPolynomialMeasure (μ : Measure ℝ) (ω : ℝ[X])
    (hω : ∀ᵐ x ∂μ, 0 < ω.eval x) (f : ℝ → ℝ) :
    (∫ x, f x ∂dividedPolynomialMeasure μ ω) = ∫ x, f x / ω.eval x ∂μ := by
  rw [dividedPolynomialMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hω] with x hx
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hx.le), smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Polynomial exactness of the divided measure is equivalent to exactness
of all fixed-denominator rational functions of the same numerator degree,
after multiplying each quadrature weight by its denominator value.
Source: Gautschi (2004), rational Gauss quadrature; operator derivations AQ36.
atlas: rational-gauss-quadrature (partial) -/
theorem polynomial_exactness_iff_rational_exactness (μ : Measure ℝ) (ω : ℝ[X])
    (hω : ∀ᵐ x ∂μ, 0 < ω.eval x) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v w : ι → ℝ) (hv : ∀ i ∈ s, ω.eval (v i) ≠ 0) (d : ℕ) :
    (∀ p : ℝ[X], p.degree < d →
      (∫ x, p.eval x ∂dividedPolynomialMeasure μ ω) = ∑ i ∈ s, w i * p.eval (v i)) ↔
      (∀ p : ℝ[X], p.degree < d →
        (∫ x, p.eval x / ω.eval x ∂μ) =
          ∑ i ∈ s, (w i * ω.eval (v i)) * (p.eval (v i) / ω.eval (v i))) := by
  have he (p : ℝ[X]) : (∑ i ∈ s, (w i * ω.eval (v i)) *
      (p.eval (v i) / ω.eval (v i))) = ∑ i ∈ s, w i * p.eval (v i) := by
    apply sum_congr rfl
    intro i hi
    field_simp [hv i hi]
  simp_rw [integral_dividedPolynomialMeasure μ ω hω, he]

/-- A prescribed rational rule is exact if and only if the weights divided
by the denominator are polynomial-exact for the reciprocal-density measure.
Source: the converse rational Gauss implication; operator derivations AQ36.
atlas: rational-gauss-quadrature (partial) -/
theorem rational_exactness_iff_divided_weights_exactness (μ : Measure ℝ) (ω : ℝ[X])
    (hω : ∀ᵐ x ∂μ, 0 < ω.eval x) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v w : ι → ℝ) (hv : ∀ i ∈ s, ω.eval (v i) ≠ 0) (d : ℕ) :
    (∀ p : ℝ[X], p.degree < d → (∫ x, p.eval x / ω.eval x ∂μ) =
      ∑ i ∈ s, w i * (p.eval (v i) / ω.eval (v i))) ↔
      (∀ p : ℝ[X], p.degree < d →
        (∫ x, p.eval x ∂dividedPolynomialMeasure μ ω) =
          ∑ i ∈ s, (w i / ω.eval (v i)) * p.eval (v i)) := by
  have he := polynomial_exactness_iff_rational_exactness μ ω hω s v
    (fun i => w i / ω.eval (v i)) hv d
  have hw : ∀ i ∈ s, (w i / ω.eval (v i)) * ω.eval (v i) = w i := by
    intro i hi
    exact div_mul_cancel₀ _ (hv i hi)
  have hsum (p : ℝ[X]) :
      (∑ i ∈ s, ((w i / ω.eval (v i)) * ω.eval (v i)) *
        (p.eval (v i) / ω.eval (v i))) =
      ∑ i ∈ s, w i * (p.eval (v i) / ω.eval (v i)) := by
    apply sum_congr rfl
    intro i hi
    rw [hw i hi]
  simpa only [hsum] using he.symm

end NLAlib

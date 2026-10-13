import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Chebyshev coefficient and truncation definitions

The arcsine-measure coefficient normalization, its weighted and cosine integral bridges,
and its finite polynomial truncation.
This is the vocabulary for atlas `chebyshev-coefficients-def`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real MeasureTheory

namespace NLAlib

/-- Real Chebyshev coefficient with zeroth normalization `1/π` and positive normalization
`2/π`, using the arcsine weight. Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def (partial) -/
def chebyshevCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 else 2) / Real.pi *
    ∫ x, f x * (T ℝ (k : ℤ)).eval x ∂measureT

/-- The arcsine-measure coefficient is the classical weighted integral on `[-1,1]`.
Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevCoeff_eq_weighted_integral (f : ℝ → ℝ) (k : ℕ) :
    chebyshevCoeff f k = (if k = 0 then 1 else 2) / Real.pi *
      ∫ x in (-1 : ℝ)..1, (f x * (T ℝ (k : ℤ)).eval x) * Real.sqrt (1 - x ^ 2)⁻¹ := by
  rw [chebyshevCoeff, integral_measureT]

/-- The weighted coefficient is the usual cosine coefficient, including the zeroth
normalization. Source: the cosine substitution for the Chebyshev weight.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevCoeff_eq_cosine_integral (f : ℝ → ℝ) (k : ℕ) :
    chebyshevCoeff f k = (if k = 0 then 1 else 2) / Real.pi *
      ∫ θ in 0..Real.pi, f (Real.cos θ) * Real.cos ((k : ℝ) * θ) := by
  rw [chebyshevCoeff, integral_measureT_eq_integral_cos]
  simp_rw [T_real_cos, Int.cast_natCast]

/-- The degree-`n` partial sum of the Chebyshev expansion.
Source: Trefethen, ATAP, Chapter 3, Theorem 3.1.
atlas: chebyshev-coefficients-def (partial) -/
def chebyshevTrunc (f : ℝ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C (chebyshevCoeff f k) * T ℝ (k : ℤ)

/-- Integer-order modified Bessel coefficient, defined by its cosine integral.
Source: Trefethen, ATAP, Exercise 3.15.
atlas: chebyshev-series-exp-bessel (partial) -/
def modifiedBesselCoeff (a : ℝ) (k : ℕ) : ℝ :=
  1 / Real.pi * ∫ θ in 0..Real.pi, Real.exp (a * Real.cos θ) * Real.cos ((k : ℝ) * θ)

/-- The Cesàro mean of the first `n+1` genuine Chebyshev truncations.
Source: Trefethen, ATAP, Exercise 6.6. -/
def fejerChebyshevMean (f : ℝ → ℝ) (n : ℕ) : ℝ[X] :=
  (n + 1 : ℝ)⁻¹ • ∑ m ∈ range (n + 1), chebyshevTrunc f m

/-- Affine transplantation from the unit interval to `[a,b]` on the complex plane.
Source: Trefethen, ATAP, Ch. 8; helper for `slit-plane-analytic-approx`. -/
def bernsteinIntervalMap (a b : ℝ) (z : ℂ) : ℂ :=
  (((b - a : ℝ) : ℂ) * z + (b + a : ℝ)) / 2

/-- Lower real-part bound of the Bernstein ellipse transplanted to `[a,b]`.
Source: Trefethen, ATAP, Ch. 8; helper for `slit-plane-analytic-approx`. -/
def bernsteinIntervalLower (a b ρ : ℝ) : ℝ :=
  (b + a - (b - a) * ((ρ + ρ⁻¹) / 2)) / 2

/-- Upper modulus bound of the Bernstein ellipse transplanted to a positive interval `[a,b]`.
Source: Trefethen, ATAP, Ch. 8; helper for `slit-plane-analytic-approx`. -/
def bernsteinIntervalUpper (a b ρ : ℝ) : ℝ :=
  (b + a + (b - a) * ((ρ + ρ⁻¹) / 2)) / 2

end NLAlib

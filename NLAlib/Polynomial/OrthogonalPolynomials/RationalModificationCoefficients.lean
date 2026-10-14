import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationMeasure
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientIdentities

/-! # Native recurrence coefficients after rational modification

Once the actual coefficient/determinant system constructs the modified monic
polynomials, their next coefficients and original-measure weighted norms give
the recurrence coefficients. Source: focused mathematical reroutes, Section 4.
-/

noncomputable section
open Polynomial MeasureTheory
namespace NLAlib

/-- The modified diagonal recurrence coefficient is the difference of successive
modified monic next coefficients, including the order-zero convention.
Source: focused mathematical reroutes, recurrence recovery after CU9.
atlas: christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceAlpha_weightedDivided_eq_sub_nextCoeff
    (μ : Measure ℝ) (u v : ℝ[X]) (hdiv : HasDividedPolynomialMoments μ v) (n : ℕ)
    (hn : ∀ k ≤ n+1, hankelMomentDet
      (polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u) k ≠ 0) :
    orthogonalRecurrenceAlpha (polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u) n =
      (monicOrthogonalPolynomial (polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u) n).nextCoeff -
      (monicOrthogonalPolynomial (polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u) (n+1)).nextCoeff :=
  orthogonalRecurrenceAlpha_eq_sub_nextCoeff _ _ hn

/-- Every positive-order modified monic subdiagonal is exactly the ratio of
its original-measure rationally weighted squared norms. At valid modified
orders source positivity makes the denominator positive.
Source: focused mathematical reroutes, recurrence recovery after CU9.
atlas: christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceBeta_weightedDivided_eq_integral_ratio
    (μ : Measure ℝ) (u v : ℝ[X]) (hdiv : HasDividedPolynomialMoments μ v) (n : ℕ) :
    let L := polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u
    orthogonalRecurrenceBeta L (n+1) =
      (∫ x, u.eval x * ((monicOrthogonalPolynomial L (n+1)).eval x)^2/v.eval x ∂μ) /
        (∫ x, u.eval x * ((monicOrthogonalPolynomial L n).eval x)^2/v.eval x ∂μ) := by
  simp only [orthogonalRecurrenceBeta, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    if_false, Nat.add_sub_cancel, orthogonalPolynomialNorm,
    polynomialWeightedFunctional_dividedPolynomialIntegral_apply, eval_pow]

end NLAlib

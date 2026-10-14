import NLAlib.Polynomial.Quadrature.EndpointJacobiData

/-! # Discrete polynomial pairings of actual endpoint rules

Exactness transfers every polynomial pairing within the degree threshold to
the constructed eigenvalue rule. This is the general discrete orthogonality
statement, with no normalization convention or extra moment assumed.
-/

noncomputable section
open Polynomial MeasureTheory Finset

namespace NLAlib

/-- The actual Lobatto rule reproduces every original polynomial pairing whose
total degree is at most `2q+1`. In particular, original orthogonal polynomial
pairs have the same discrete orthogonality whenever their degree sum lies in
this range. Source: Gautschi (2004), Theorem 1.23; operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem sum_lobattoWeights_mul_eval_mul_eval_eq_integral {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) {p r : ℝ[X]} (hpr : p.degree + r.degree < (2 * q + 2 : ℕ)) :
    (∑ i, lobattoWeights (polynomialIntegral μ hμ) q a c i *
      p.eval (lobattoNodes (polynomialIntegral μ hμ) q a c i) *
      r.eval (lobattoNodes (polynomialIntegral μ hμ) q a c i)) =
      ∫ x, p.eval x * r.eval x ∂μ := by
  simpa only [eval_mul, mul_assoc] using
    (integral_eval_eq_sum_lobattoWeights_mul_eval hμ q hs a c (p := p * r)
      (by simpa only [degree_mul] using hpr)).symm

end NLAlib

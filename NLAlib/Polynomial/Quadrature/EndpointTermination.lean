import NLAlib.Polynomial.Quadrature.GaussMeasureRemainder

/-! # The actual terminal rule as the endpoint-border fallback

When endpoint shifts cease to be invertible at finite support, the canonical
terminal spectral rule already integrates every function. This theorem constructs
that rule from the original measure; it assumes no exactness certificate or
smoothness and never divides by a vanishing endpoint determinant.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- The actual terminal Gauss nodes and weights integrate every function. They
supply the finite-support fallback when a nondegenerate endpoint Schur border is
unavailable. Source: focused mathematical reroutes, Section 3, terminal branch.
atlas: gauss-radau-lobatto (partial), gauss-quadrature-derivative-remainder (partial) -/
theorem integral_eq_gaussRule_of_support_encard {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : μ.support.encard = (n : ℕ∞)) (f : ℝ → ℝ) :
    let hMom := hasPolynomialMoments_of_ae_mem_Icc hμ
    (∫ x, f x ∂μ) = ∑ i : Fin n, gaussWeights μ hMom n i * f (gaussNodes μ hMom n i) := by
  dsimp only
  let hMom := hasPolynomialMoments_of_ae_mem_Icc hμ
  have hs : (n : ℕ∞) ≤ μ.support.encard := hn.ge
  have hfinite := Set.finite_of_encard_eq_coe hn
  have hncard : hfinite.toFinset.card = n := by
    exact_mod_cast (hfinite.encard_eq_coe_toFinset_card.symm.trans hn)
  have hzero := orthogonalPolynomialNorm_eq_zero_of_finite_support μ hMom hfinite
  rw [hncard] at hzero
  have hnodalzero : (∫ x, (Lagrange.nodal univ (gaussNodes μ hMom n)).eval x ^ 2 ∂μ) = 0 := by
    rw [nodal_gaussNodes_eq_monicOrthogonalPolynomial hMom hs]
    simpa only [orthogonalPolynomialNorm, polynomialIntegral_apply, eval_pow] using hzero
  exact integral_eq_quadrature_of_integral_nodal_sq_eq_zero hμ hn0
    (gaussNodes μ hMom n) (gaussWeights μ hMom n) (gaussNodes_injective hMom hs)
    (fun p hp => integral_eval_eq_sum_gaussWeights_mul_eval hMom hn0 hs hp) hnodalzero f

end NLAlib

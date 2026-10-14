import NLAlib.Polynomial.Quadrature.EndpointJacobiMoments
import NLAlib.Polynomial.Quadrature.RootedMomentRule

/-! # Polynomial exactness of the constructed endpoint matrix rules

The actual Radau and Lobatto matrices are Hermitian. Their rooted moment identities
prove exactness of the first-coordinate functional calculus and hence of their
Golub–Welsch eigenvalue sums.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

theorem isHermitian_leftRadauJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a : ℝ) :
    (leftRadauJacobiMatrix L q a).IsHermitian :=
  isHermitian_finSymmetricBorder (isHermitian_orthogonalPolynomialJacobiMatrix L q) _ _

theorem isHermitian_rightRadauJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (c : ℝ) :
    (rightRadauJacobiMatrix L q c).IsHermitian :=
  isHermitian_finSymmetricBorder (isHermitian_orthogonalPolynomialJacobiMatrix L q) _ _

theorem isHermitian_lobattoJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a c : ℝ) :
    (lobattoJacobiMatrix L q a c).IsHermitian :=
  isHermitian_finSymmetricBorder (isHermitian_orthogonalPolynomialJacobiMatrix L (q + 1)) _ _

/-- The actual left Radau Schur matrix rule integrates every polynomial through
degree `2q`; its exactness follows from construction, including the `q=0` rule.
Source: focused mathematical reroutes, Section 3 (BL5), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_mass_mul_cfc_leftRadauJacobiMatrix {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 1 : ℕ)) :
    (∫ x, p.eval x ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) *
      cfc p.eval (leftRadauJacobiMatrix (polynomialIntegral μ hμ) q a) 0 0 := by
  apply integral_eval_eq_mass_mul_cfc_of_rooted_moments hμ (Nat.succ_pos q)
    (isHermitian_leftRadauJacobiMatrix _ _ _) (2 * q + 1) _ hp
  intro k hk
  exact (integral_pow_eq_mass_mul_radauJacobiMatrix_pow hμ q hs a a (by omega)).1

/-- The actual right Radau Schur matrix rule integrates every polynomial through
degree `2q`. Source: focused mathematical reroutes, Section 3 (BL5), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_mass_mul_cfc_rightRadauJacobiMatrix {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (c : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 1 : ℕ)) :
    (∫ x, p.eval x ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) *
      cfc p.eval (rightRadauJacobiMatrix (polynomialIntegral μ hμ) q c) 0 0 := by
  apply integral_eval_eq_mass_mul_cfc_of_rooted_moments hμ (Nat.succ_pos q)
    (isHermitian_rightRadauJacobiMatrix _ _ _) (2 * q + 1) _ hp
  intro k hk
  exact (integral_pow_eq_mass_mul_radauJacobiMatrix_pow hμ q hs c c (by omega)).2

/-- The actual Lobatto Schur matrix rule integrates every polynomial through
degree `2q+1`, including `q=0`. Source: focused reroutes, Section 3 (BL10), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_mass_mul_cfc_lobattoJacobiMatrix {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 2 : ℕ)) :
    (∫ x, p.eval x ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) *
      cfc p.eval (lobattoJacobiMatrix (polynomialIntegral μ hμ) q a c) 0 0 := by
  apply integral_eval_eq_mass_mul_cfc_of_rooted_moments hμ (by omega : 0 < q + 2)
    (isHermitian_lobattoJacobiMatrix _ _ _ _) (2 * q + 2) _ hp
  intro k hk
  exact integral_pow_eq_mass_mul_lobattoJacobiMatrix_pow hμ q hs a c (by omega)

end NLAlib

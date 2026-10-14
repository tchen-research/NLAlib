import NLAlib.Polynomial.OrthogonalPolynomials.SecondKind
import NLAlib.Polynomial.Quadrature.GaussMeasure

/-! # Actual Gauss weights as second-kind residues

Distinct canonical Gauss nodes make the derivative denominator nonzero. The
finite divided-difference formula therefore gives the actual integrated-cardinal
weight as the second-kind residue. Source: Gautschi (2004), Chapter 1, AQ18.
-/

noncomputable section
open Polynomial MeasureTheory Finset
namespace NLAlib

/-- The actual Gauss weight is the second-kind numerator divided by the
derivative of the actual monic denominator at its simple node. The derivative's
nonvanishing is proved from the constructed distinct nodes. Source: AQ18.
atlas: jacobi-fraction-second-kind (partial) -/
theorem gaussWeights_eq_secondKindPolynomial_div_derivative
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    gaussWeights μ hμ n i =
      (secondKindPolynomial (polynomialIntegral μ hμ) n).eval (gaussNodes μ hμ n i) /
        (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).derivative.eval (gaussNodes μ hμ n i) := by
  have hn0 : 0 < n := by have := i.isLt; omega
  have hL : ∀ k ≤ n, hankelMomentDet (polynomialIntegral μ hμ) k ≠ 0 := fun k hk =>
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn)
  have hnum := eval_secondKindPolynomial_at_node (polynomialIntegral μ hμ) n hn0 hL
    (gaussNodes μ hμ n) (gaussWeights μ hμ n) (gaussNodes_injective hμ hn)
    (fun j => (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨j,rfl⟩)
    (fun p hp => integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn
      (hp.trans_le (by exact_mod_cast (show n ≤ 2*n by omega)))) i
  have hder : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).derivative.eval
      (gaussNodes μ hμ n i) ≠ 0 := by
    rw [← nodal_gaussNodes_eq_monicOrthogonalPolynomial hμ hn]
    have h := Lagrange.nodalWeight_ne_zero (gaussNodes_injective hμ hn).injOn (mem_univ i)
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)] at h
    intro hd
    rw [hd, inv_zero] at h
    exact h rfl
  rw [hnum, mul_div_cancel_right₀ _ hder]

end NLAlib

import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMoments
import NLAlib.Polynomial.Quadrature.GaussMeasure
import NLAlib.Matrix.Functions.PolynomialCalculus

/-! # Original-measure Gauss weights in the canonical Jacobi eigenbasis

The full finite moment bridge evaluates every cardinal polynomial in the
Jacobi matrix. Its spectral decomposition identifies the integrated-cardinal
weight with the original mass times the squared first eigenvector coordinate.
-/

noncomputable section

open Polynomial Matrix MeasureTheory Finset
open scoped Matrix

namespace NLAlib

/-- The actual cardinal weight of a general positive measure has the
Golub–Welsch formula with the original measure mass included.
Source: Gautschi (2004), Theorem 1.46.
atlas: gauss-christoffel-numbers (partial), jacobi-fraction-second-kind (partial) -/
theorem gaussWeights_eq_mass_mul_sq_eigenvectorBasis_apply_zero
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : 0 < n)
    (hs : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    gaussWeights μ hμ n i = (∫ _ : ℝ, (1 : ℝ) ∂μ) *
      (((isHermitian_orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n).eigenvectorBasis i :
        Fin n → ℝ) ⟨0, hn⟩) ^ 2 := by
  let L := polynomialIntegral μ hμ
  let hJ := isHermitian_orthogonalPolynomialJacobiMatrix L n
  let p := Lagrange.basis univ (gaussNodes μ hμ n) i
  have hd : p.degree < (2 * n : ℕ) := by
    rw [Lagrange.degree_basis (gaussNodes_injective hμ hs).injOn (mem_univ i), card_univ,
      Fintype.card_fin]
    exact_mod_cast (show n - 1 < 2 * n by omega)
  have hm := functional_eq_mass_mul_aeval_jacobi_apply_zero_zero L hn
    (fun j hj => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hj : (j : ℕ∞) ≤ n).trans hs))
    (fun j hj => orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast Nat.succ_le_of_lt hj : (j + 1 : ℕ∞) ≤ n).trans hs)) hd
  have hc := dotProduct_aeval_mulVec_eq_sum hJ p (Pi.single ⟨0, hn⟩ 1)
  rw [dotProduct_comm, dotProduct_single_one, Matrix.mulVec_single_one] at hc
  simp only [dotProduct_single_one] at hc
  change (aeval (orthogonalPolynomialJacobiMatrix L n) p) ⟨0, hn⟩ ⟨0, hn⟩ = _ at hc
  have hnodes : hJ.eigenvalues = gaussNodes μ hμ n := rfl
  rw [hnodes] at hc
  rw [Finset.sum_eq_single i] at hc
  · rw [show p.eval (gaussNodes μ hμ n i) = 1 from
      Lagrange.eval_basis_self (gaussNodes_injective hμ hs).injOn (mem_univ i), one_mul] at hc
    rw [hc] at hm
    simpa only [L, p, gaussWeights, momentGaussWeights, gaussNodes, momentGaussNodes,
      polynomialIntegral_apply, eval_one] using hm
  · intro j _ hji
    rw [show p.eval (gaussNodes μ hμ n j) = 0 from
      Lagrange.eval_basis_of_ne hji.symm (mem_univ j), zero_mul]
  · simp

end NLAlib

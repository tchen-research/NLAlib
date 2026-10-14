import NLAlib.Polynomial.OrthogonalPolynomials.MomentContinuity
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import NLAlib.Matrix.Perturbation.EigenvalueContinuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Continuous moment Jacobi matrices and nodes

The finite normalized multiplication matrix depends continuously on the moments
at positive-norm systems. Ordered Hermitian eigenvalue continuity supplies the
node convergence without choosing eigenvectors. Source: AQ22–AQ23 in the
operator re-derivations, Gautschi (2004), §2.1.
-/

noncomputable section
open Polynomial
namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : E → (ℝ[X] →ₗ[ℝ] ℝ)} {x : E} {n : ℕ}

/-- Coefficients of normalized moment polynomials are smooth at positive norm. -/
theorem contDiffAt_coeff_orthonormalMomentPolynomial
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0)
    (hh : 0 < orthogonalPolynomialNorm (L x) n) (k : ℕ) :
    ContDiffAt ℝ 1 (fun y => (orthonormalMomentPolynomial (L y) n).coeff k) x := by
  simp only [orthonormalMomentPolynomial, coeff_C_mul]
  exact ((contDiffAt_orthogonalPolynomialNorm hL hn).sqrt hh.ne').inv
    (Real.sqrt_pos.mpr hh).ne' |>.mul (contDiffAt_coeff_monicOrthogonalPolynomial hL hn k)

/-- Each actual finite moment Jacobi entry is continuous at a nonsingular,
positive-norm system. -/
theorem continuousAt_orthogonalPolynomialJacobiMatrix_apply
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : ∀ k < n, hankelMomentDet (L x) k ≠ 0)
    (hh : ∀ k < n, 0 < orthogonalPolynomialNorm (L x) k) (i j : Fin n) :
    ContinuousAt (fun y => orthogonalPolynomialJacobiMatrix (L y) n i j) x := by
  unfold orthogonalPolynomialJacobiMatrix
  suffices h : ContDiffAt ℝ 1 (fun y =>
      L y (X * orthonormalMomentPolynomial (L y) j.val *
        orthonormalMomentPolynomial (L y) i.val)) x from h.continuousAt
  apply contDiffAt_functional_polynomial_of_degree_lt (d := 2 * n + 2)
  · intro y
    have hd (k : ℕ) : (orthonormalMomentPolynomial (L y) k).degree ≤ k := by
      rw [orthonormalMomentPolynomial, C_mul']
      apply (degree_smul_le _ _).trans_eq
      rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) k).ne_zero,
        natDegree_monicOrthogonalPolynomial]
    apply (degree_mul_le _ _).trans_lt
    apply (add_le_add ((degree_mul_le _ _).trans
      (add_le_add (by rw [degree_X]) (hd j.val))) (hd i.val)).trans_lt
    exact_mod_cast (show 1 + j.val + i.val < 2 * n + 2 by have := i.isLt; have := j.isLt; omega)
  · intro k
    apply contDiffAt_coeff_mul
    · apply contDiffAt_coeff_mul (fun _ => contDiffAt_const)
      exact contDiffAt_coeff_orthonormalMomentPolynomial hL (hn j.val j.isLt) (hh j.val j.isLt)
    · exact contDiffAt_coeff_orthonormalMomentPolynomial hL (hn i.val i.isLt) (hh i.val i.isLt)
  · exact fun k => hL k.val

/-- The canonically indexed real nodes of a finite moment Jacobi matrix are
continuous at each nonsingular positive-norm system. Source: AQ22–AQ23.
atlas: recurrence-coefficient-continuity (partial) -/
theorem continuousAt_eigenvalues_orthogonalPolynomialJacobiMatrix
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : ∀ k < n, hankelMomentDet (L x) k ≠ 0)
    (hh : ∀ k < n, 0 < orthogonalPolynomialNorm (L x) k) (i : Fin n) :
    ContinuousAt (fun y =>
      (isHermitian_orthogonalPolynomialJacobiMatrix (L y) n).eigenvalues i) x := by
  exact Matrix.IsHermitian.continuousAt_eigenvalues₀
    (fun y => isHermitian_orthogonalPolynomialJacobiMatrix (L y) n)
    (continuousAt_orthogonalPolynomialJacobiMatrix_apply hL hn hh)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

end NLAlib

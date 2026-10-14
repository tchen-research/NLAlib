import NLAlib.Polynomial.OrthogonalPolynomials.MomentDerivative

/-!
# First variation of canonical monic norms

The derivative of a monic polynomial has smaller degree. Orthogonality therefore
removes the polynomial-variation terms from the derivative of its squared norm.
Source: Gautschi (2004), §2.1; AQ26–AQ27 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

/-- The coefficient derivative of a canonical monic polynomial family, containing
only its lower-degree part because the leading coefficient is constantly one. -/
def monicOrthogonalPolynomialDeriv
    (L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)) (n : ℕ) (x : ℝ) : ℝ[X] :=
  ∑ i : Fin n, monomial i.val
    (deriv (fun y => orthogonalPolynomialCoefficients (L y) n i) x)

/-- The variation of a monic order-`n` polynomial has degree below `n`, also at
order zero, where it is the zero polynomial. -/
theorem degree_monicOrthogonalPolynomialDeriv_lt
    (L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)) (n : ℕ) (x : ℝ) :
    (monicOrthogonalPolynomialDeriv L n x).degree < n :=
  degree_sum_monomial_fin_lt _

/-- The actual canonical moment-system family has the coefficient derivative
given by the lower coefficient variations. -/
theorem hasPolynomialDerivAt_monicOrthogonalPolynomial
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) :
    HasCoeffDerivAt (fun y => monicOrthogonalPolynomial (L y) n)
      (monicOrthogonalPolynomialDeriv L n x) x := by
  have hc (i : Fin n) :=
    (contDiffAt_orthogonalPolynomialCoefficients hL hn i).differentiableAt (by norm_num)
  intro k
  simp only [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart,
    monicOrthogonalPolynomialDeriv, coeff_add, finsetSum_coeff, coeff_monomial]
  convert (hasDerivAt_const x ((X ^ n : ℝ[X]).coeff k)).add
    (HasDerivAt.fun_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      show HasDerivAt (fun y => if i.val = k then
          orthogonalPolynomialCoefficients (L y) n i else 0)
        (if i.val = k then deriv (fun y => orthogonalPolynomialCoefficients (L y) n i) x
          else 0) x from by
        split_ifs
        · exact (hc i).hasDerivAt
        · exact hasDerivAt_const x 0)) using 1
  all_goals first | rfl | simp

/-- The first variation of the canonical squared monic norm is the functional
variation evaluated on its squared polynomial. The coefficient variations cancel
by lower-degree orthogonality. Source: AQ27.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_orthogonalPolynomialNorm
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) :
    HasDerivAt (fun y => orthogonalPolynomialNorm (L y) n)
      (D (monicOrthogonalPolynomial (L x) n ^ 2)) x := by
  let P := fun y => monicOrthogonalPolynomial (L y) n
  let V := monicOrthogonalPolynomialDeriv L n x
  have hP := hasPolynomialDerivAt_monicOrthogonalPolynomial hL hn
  have hVdeg : V.degree < n := degree_monicOrthogonalPolynomialDeriv_lt L n x
  have hPdeg (y : ℝ) : (P y).degree = n := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hnn : (n : WithBot ℕ) + n < ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast (show n + n < 2 * n + 1 by omega)
  have hVp : (V * P x + P x * V).degree < (2 * n + 1 : ℕ) := by
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · apply (degree_mul_le _ _).trans_lt
      rw [hPdeg]
      exact (add_le_add hVdeg.le (le_rfl : (n : WithBot ℕ) ≤ n)).trans_lt hnn
    · apply (degree_mul_le _ _).trans_lt
      rw [hPdeg]
      exact (add_le_add (le_rfl : (n : WithBot ℕ) ≤ n) hVdeg.le).trans_lt hnn
  have h := hasDerivAt_functional_polynomial (d := 2 * n + 1)
    (p := fun y => P y * P y) (p' := V * P x + P x * V)
    (by intro y; rw [degree_mul, hPdeg]; norm_cast; omega) hVp (hP.mul hP) hD
  have horth := (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (L x) hn).orthogonal V hVdeg
  have hv : L x (V * P x + P x * V) = 0 := by
    rw [map_add, mul_comm V]
    simp only [P, horth, add_zero]
  simpa only [orthogonalPolynomialNorm, pow_two, hv, add_zero] using h

end NLAlib

import NLAlib.Polynomial.OrthogonalPolynomials.AlphaSensitivity
import NLAlib.Polynomial.OrthogonalPolynomials.BetaSensitivity

/-! # Degree bounds of actual recurrence sensitivity polynomials

Every included alpha sensitivity is below degree `2n`, including the highest
diagonal, and every included beta sensitivity is below the same bound. These
bounds justify using the dual coordinates of an arbitrary degree-`2n` fixed
polynomial basis. Source: operator re-derivations AQ28--AQ31.
-/

noncomputable section
open Polynomial
namespace NLAlib

private theorem degree_monic_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) :
    (monicOrthogonalPolynomial L k).degree = (k : WithBot ℕ) := by
  rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial]

/-- Alpha sensitivity uses degree at most `2k+1`, without normalization of the
next orthogonal polynomial. Source: AQ29--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem degree_orthogonalRecurrenceAlphaSensitivityPolynomial_le
    (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) :
    (orthogonalRecurrenceAlphaSensitivityPolynomial L k).degree ≤ ((2*k+1 : ℕ) : WithBot ℕ) := by
  unfold orthogonalRecurrenceAlphaSensitivityPolynomial
  rw [C_mul']
  apply (degree_smul_le _ _).trans
  apply (degree_sub_le _ _).trans
  apply max_le
  · rw [degree_mul, degree_X_sub_C, degree_pow, degree_monic_eq, nsmul_eq_mul]
    norm_cast
    omega
  · rw [C_mul']
    apply (degree_smul_le _ _).trans
    rw [degree_mul, degree_monic_eq, degree_monic_eq]
    exact_mod_cast (show k - 1 + k ≤ 2*k + 1 by omega)

/-- Beta sensitivity uses degree at most `2k`, including the total zero-order
boundary. Source: AQ28--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem degree_orthogonalRecurrenceBetaSensitivityPolynomial_le
    (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) :
    (orthogonalRecurrenceBetaSensitivityPolynomial L k).degree ≤ ((2*k : ℕ) : WithBot ℕ) := by
  unfold orthogonalRecurrenceBetaSensitivityPolynomial
  rw [C_mul']
  apply (degree_smul_le _ _).trans
  apply (degree_sub_le _ _).trans
  apply max_le
  · rw [C_mul']
    apply (degree_smul_le _ _).trans
    rw [degree_pow, degree_monic_eq, nsmul_eq_mul]
    norm_cast
  · rw [C_mul']
    apply (degree_smul_le _ _).trans
    rw [degree_pow, degree_monic_eq, nsmul_eq_mul]
    exact_mod_cast (show 2*(k - 1) ≤ 2*k by omega)

end NLAlib

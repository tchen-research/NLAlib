import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence

/-! # Coefficient identities for monic orthogonal recurrences

The diagonal recurrence coefficient is the difference of successive
second-highest polynomial coefficients. Constants use Mathlib's zero
`nextCoeff`, so the same identity includes the order-zero boundary.
Source: Gautschi (2004), Theorem 1.27.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The monic recurrence diagonal is the difference of successive
second-highest coefficients, including order zero.
Source: Gautschi (2004), Theorem 1.27. -/
theorem orthogonalRecurrenceAlpha_eq_sub_nextCoeff
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) :
    orthogonalRecurrenceAlpha L n =
      (monicOrthogonalPolynomial L n).nextCoeff -
        (monicOrthogonalPolynomial L (n + 1)).nextCoeff := by
  cases n with
  | zero =>
    have h := monicOrthogonalPolynomial_succ_eq L 0 hL
    simp [monicOrthogonalPolynomial_zero, orthogonalRecurrenceBeta] at h
    rw [h, nextCoeff_X_sub_C, monicOrthogonalPolynomial_zero]
    rw [show (1 : 𝕜[X]).nextCoeff = 0 by
      simpa only [C_1] using nextCoeff_C_eq_zero (1 : 𝕜)]
    ring
  | succ n =>
    have hrec := monicOrthogonalPolynomial_succ_eq L (n + 1) hL
    rw [sub_mul] at hrec
    have h := congrArg (fun p : 𝕜[X] => p.coeff (n + 1)) hrec
    simp only [coeff_sub, coeff_C_mul, coeff_X_mul, Nat.add_sub_cancel] at h
    have htop : (monicOrthogonalPolynomial L (n + 1)).coeff (n + 1) = 1 := by
      simpa only [natDegree_monicOrthogonalPolynomial] using
        (monic_monicOrthogonalPolynomial L (n + 1)).coeff_natDegree
    have hlow : (monicOrthogonalPolynomial L n).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_monicOrthogonalPolynomial]; omega)
    rw [htop, hlow, mul_one, mul_zero, sub_zero] at h
    rw [nextCoeff_of_natDegree_pos (by rw [natDegree_monicOrthogonalPolynomial]; omega),
      nextCoeff_of_natDegree_pos (by rw [natDegree_monicOrthogonalPolynomial]; omega),
      natDegree_monicOrthogonalPolynomial, natDegree_monicOrthogonalPolynomial,
      Nat.add_sub_cancel, show n + 1 + 1 - 1 = n + 1 by omega]
    linear_combination h

end NLAlib

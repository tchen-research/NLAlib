import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientIdentities

/-! # Christoffel quotient and elimination coefficients

The exact linear modification determines both recurrence coefficients. The
quotient `q_n=-π_(n+1)(z)/π_n(z)` and elimination `e_n=β_(n+1)/q_n` give the
usual Darboux coefficient identities without an unjustified value-at-`z` claim.
Source: Gautschi (2004), Theorem 1.33; operator derivations OP20–OP24.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The negative ratio of consecutive monic polynomial values at a modification
point. The total value is zero if the denominator vanishes. -/
def christoffelQuotient (L : 𝕜[X] →ₗ[𝕜] 𝕜) (z : 𝕜) (n : ℕ) : 𝕜 :=
  -(monicOrthogonalPolynomial L (n + 1)).eval z / (monicOrthogonalPolynomial L n).eval z

/-- The elimination coefficient for the next monic subdiagonal. Its total
value is zero when the corresponding quotient vanishes. -/
def christoffelElimination (L : 𝕜[X] →ₗ[𝕜] 𝕜) (z : 𝕜) (n : ℕ) : 𝕜 :=
  orthogonalRecurrenceBeta L (n + 1) / christoffelQuotient L z n

private theorem nextCoeff_christoffelPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    (christoffelPolynomial L z n).nextCoeff =
      (monicOrthogonalPolynomial L (n + 1)).nextCoeff + z + christoffelQuotient L z n := by
  have hP := isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz
  have hproddeg : ((X - C z) * christoffelPolynomial L z n).natDegree = n + 1 := by
    rw [natDegree_mul (monic_X_sub_C z).ne_zero hP.monic.ne_zero,
      natDegree_X_sub_C, hP.natDegree_eq]
    omega
  have hnext : ((X - C z) * christoffelPolynomial L z n).coeff n =
      -z + (christoffelPolynomial L z n).nextCoeff := by
    have h := (monic_X_sub_C z).nextCoeff_mul hP.monic
    rw [nextCoeff_of_natDegree_pos (by rw [hproddeg]; omega), hproddeg,
      Nat.add_sub_cancel, nextCoeff_X_sub_C] at h
    exact h
  have h := congrArg (fun p : 𝕜[X] => p.coeff n) (X_sub_C_mul_christoffelPolynomial L n hz)
  rw [hnext, coeff_sub, coeff_C_mul] at h
  have htop : (monicOrthogonalPolynomial L n).coeff n = 1 := by
    simpa only [natDegree_monicOrthogonalPolynomial] using
      (monic_monicOrthogonalPolynomial L n).coeff_natDegree
  rw [htop, mul_one] at h
  have hnextold : (monicOrthogonalPolynomial L (n + 1)).coeff n =
      (monicOrthogonalPolynomial L (n + 1)).nextCoeff := by
    rw [nextCoeff_of_natDegree_pos (by rw [natDegree_monicOrthogonalPolynomial]; omega),
      natDegree_monicOrthogonalPolynomial, Nat.add_sub_cancel]
  rw [hnextold] at h
  rw [christoffelQuotient, neg_div]
  linear_combination h

/-- Evaluation of the original recurrence gives the quotient/elimination
diagonal identity. The order-zero elimination boundary is explicitly zero.
Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial) -/
theorem orthogonalRecurrenceAlpha_eq_add_christoffelQuotient_christoffelElimination
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) (n : ℕ) :
    orthogonalRecurrenceAlpha L n = z + christoffelQuotient L z n +
      (if n = 0 then 0 else christoffelElimination L z (n - 1)) := by
  have h := congrArg (eval z) (monicOrthogonalPolynomial_succ_eq L n (fun k _ => hL k))
  simp only [eval_sub, eval_mul, eval_X, eval_C] at h
  cases n with
  | zero =>
    simp [monicOrthogonalPolynomial_zero, orthogonalRecurrenceBeta] at h
    simp [christoffelQuotient, monicOrthogonalPolynomial_zero]
    linear_combination h
  | succ n =>
    simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, christoffelElimination,
      christoffelQuotient]
    field_simp [hz (n + 1), hz n]
    simp only [Nat.add_sub_cancel] at h
    linear_combination h

/-- The monic diagonal after a linear modification is `z+q_n+e_n`.
Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceAlpha_polynomialWeightedFunctional_X_sub_C
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) (n : ℕ) :
    orthogonalRecurrenceAlpha (polynomialWeightedFunctional L (X - C z)) n =
      z + christoffelQuotient L z n + christoffelElimination L z n := by
  have hnew := quasiDefinitePolynomialWeightedFunctional_X_sub_C hL hz
  rw [orthogonalRecurrenceAlpha_eq_sub_nextCoeff _ n (fun k _ => hnew k),
    monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C L n (fun k _ => hL k) (hz n),
    monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C L (n + 1) (fun k _ => hL k) (hz (n + 1)),
    nextCoeff_christoffelPolynomial L n (fun k _ => hL k) (hz n),
    nextCoeff_christoffelPolynomial L (n + 1) (fun k _ => hL k) (hz (n + 1))]
  have hα := orthogonalRecurrenceAlpha_eq_sub_nextCoeff L (n + 1) (fun k _ => hL k)
  have hq := orthogonalRecurrenceAlpha_eq_add_christoffelQuotient_christoffelElimination hL hz (n + 1)
  simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel] at hq
  linear_combination hq - hα

/-- The positive-order monic subdiagonal after a linear modification is
`q_n e_(n−1)`. Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceBeta_polynomialWeightedFunctional_X_sub_C
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) {n : ℕ} (hn : 0 < n) :
    orthogonalRecurrenceBeta (polynomialWeightedFunctional L (X - C z)) n =
      christoffelQuotient L z n * christoffelElimination L z (n - 1) := by
  rw [orthogonalRecurrenceBeta, if_neg hn.ne',
    orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C L n (fun k _ => hL k) (hz n),
    orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C L (n - 1) (fun k _ => hL k) (hz (n - 1)),
    christoffelElimination, show n - 1 + 1 = n by omega,
    orthogonalRecurrenceBeta, if_neg hn.ne', christoffelQuotient, christoffelQuotient]
  have hprev := orthogonalPolynomialNorm_ne_zero_of_quasiDefinite hL (n - 1)
  simp only [show n - 1 + 1 = n by omega]
  field_simp [hz n, hz (n - 1), hprev]

end NLAlib

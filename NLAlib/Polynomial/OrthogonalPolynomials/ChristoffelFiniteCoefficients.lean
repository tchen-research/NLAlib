import NLAlib.Polynomial.OrthogonalPolynomials.ChristoffelCoefficients

/-!
# Finite-order Christoffel recurrence coefficients

The quotient and elimination formulas need only the displayed finite moment
systems. In particular the last diagonal formula remains valid when the next
original squared norm is zero at finite-support termination.
Source: Gautschi (2004), Theorem 1.57; operator re-derivations AQ13–AQ15.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- Evaluating the finite original recurrence gives its quotient/elimination
diagonal formula. Only the moment systems and nonzero evaluations through
order `n+1` are needed.
Source: Gautschi (2004), Theorem 1.57; AQ14.
atlas: kernel-polynomials-christoffel (partial) -/
theorem orthogonalRecurrenceAlpha_eq_add_christoffelQuotient_christoffelElimination_of_finite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {z : 𝕜}
    (hL : ∀ k ≤ n+1, hankelMomentDet L k ≠ 0)
    (hz : ∀ k ≤ n+1, (monicOrthogonalPolynomial L k).eval z ≠ 0) :
    orthogonalRecurrenceAlpha L n = z + christoffelQuotient L z n +
      (if n = 0 then 0 else christoffelElimination L z (n-1)) := by
  have h := congrArg (eval z) (monicOrthogonalPolynomial_succ_eq L n hL)
  simp only [eval_sub, eval_mul, eval_X, eval_C] at h
  cases n with
  | zero =>
    simp [monicOrthogonalPolynomial_zero, orthogonalRecurrenceBeta] at h
    simp [christoffelQuotient, monicOrthogonalPolynomial_zero]
    linear_combination h
  | succ n =>
    simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, christoffelElimination,
      christoffelQuotient]
    field_simp [hz (n+1) (by omega), hz n (by omega)]
    simp only [Nat.add_sub_cancel] at h
    linear_combination h

/-- The modified diagonal is `z+q_n+e_n` under finite-order hypotheses, even
when the original norm at order `n+1` vanishes at finite termination.
Source: Gautschi (2004), Theorem 1.57; AQ14.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceAlpha_polynomialWeightedFunctional_X_sub_C_of_finite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {z : 𝕜}
    (hL : ∀ k ≤ n+1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0)
    (hsucc : (monicOrthogonalPolynomial L (n+1)).eval z ≠ 0) :
    orthogonalRecurrenceAlpha (polynomialWeightedFunctional L (X-C z)) n =
      z + christoffelQuotient L z n + christoffelElimination L z n := by
  let P := monicOrthogonalPolynomial L n
  let M := monicOrthogonalPolynomial L (n+1)
  let R := christoffelPolynomial L z n
  let q := christoffelQuotient L z n
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n (by omega))
  have hM := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL (n+1) le_rfl)
  have hR := isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz
  have hnorm : orthogonalPolynomialNorm L n ≠ 0 := hP.functional_sq_ne_zero (hL (n+1) le_rfl)
  have hq : q ≠ 0 := div_ne_zero (neg_ne_zero.mpr hsucc) hz
  have hPdeg : P.degree < (n+1 : ℕ) := by
    rw [degree_eq_natDegree hP.monic.ne_zero, hP.natDegree_eq]
    exact_mod_cast Nat.lt_succ_self n
  have hRdeg : R.degree < (n+1 : ℕ) := by
    rw [degree_eq_natDegree hR.monic.ne_zero, hR.natDegree_eq]
    exact_mod_cast Nat.lt_succ_self n
  have hMP : L (M*P) = 0 := hM.orthogonal P hPdeg
  have hMR : L (M*R) = 0 := hM.orthogonal R hRdeg
  have hPM : L (P*M) = 0 := by rw [mul_comm]; exact hMP
  have hPR : L (P*R) = orthogonalPolynomialNorm L n :=
    hP.functional_mul_eq_sq_of_monic hR.monic hR.natDegree_eq
  have hmul : (X-C z)*R = M+C q*P := by
    simpa only [R, M, P, q, christoffelQuotient, neg_div, map_neg,
      neg_mul, sub_eq_add_neg] using X_sub_C_mul_christoffelPolynomial L n hz
  have hXR : X*R = M+C q*P+C z*R := by linear_combination hmul
  have hnormNew : orthogonalPolynomialNorm (polynomialWeightedFunctional L (X-C z)) n =
      q * orthogonalPolynomialNorm L n := by
    simpa only [q, christoffelQuotient, neg_div] using
      orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C L n hL hz
  have hnum : polynomialWeightedFunctional L (X-C z) (X*R^2) =
      orthogonalPolynomialNorm L (n+1) + q*q*orthogonalPolynomialNorm L n +
        q*z*orthogonalPolynomialNorm L n := by
    change L ((X-C z)*(X*R^2)) = _
    rw [show (X-C z)*(X*R^2) = ((X-C z)*R)*(X*R) by ring, hmul, hXR]
    rw [show (M+C q*P)*(M+C q*P+C z*R) = M*M+C q*(M*P)+C z*(M*R)+
        C q*(P*M)+C (q*q)*(P*P)+C (q*z)*(P*R) by simp only [map_mul]; ring]
    simp only [map_add, C_mul', map_smul, smul_eq_mul, hMP, hMR, hPM, hPR,
      mul_zero, add_zero]
    simp only [orthogonalPolynomialNorm, pow_two, P, M]
  rw [orthogonalRecurrenceAlpha,
    monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C L n hL hz,
    hnormNew, hnum]
  dsimp only [christoffelElimination, orthogonalRecurrenceBeta]
  rw [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
  change (orthogonalPolynomialNorm L (n+1)+q*q*orthogonalPolynomialNorm L n+
    q*z*orthogonalPolynomialNorm L n)/(q*orthogonalPolynomialNorm L n) =
      z+q+(orthogonalPolynomialNorm L (n+1)/orthogonalPolynomialNorm L n)/q
  field_simp
  ring

/-- The modified positive-order monic subdiagonal is `q_n e_(n-1)` using only
the finite original systems and evaluations through order `n+1`.
Source: Gautschi (2004), Theorem 1.57; AQ14.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem orthogonalRecurrenceBeta_polynomialWeightedFunctional_X_sub_C_of_finite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {z : 𝕜} (hn : 0<n)
    (hL : ∀ k ≤ n+1, hankelMomentDet L k ≠ 0)
    (hz : ∀ k ≤ n+1, (monicOrthogonalPolynomial L k).eval z ≠ 0) :
    orthogonalRecurrenceBeta (polynomialWeightedFunctional L (X-C z)) n =
      christoffelQuotient L z n * christoffelElimination L z (n-1) := by
  rw [orthogonalRecurrenceBeta, if_neg hn.ne',
    orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C L n hL (hz n (by omega)),
    orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C L (n-1)
      (fun k hk => hL k (by omega)) (hz (n-1) (by omega)),
    christoffelElimination, show n-1+1 = n by omega,
    orthogonalRecurrenceBeta, if_neg hn.ne', christoffelQuotient, christoffelQuotient]
  have hprev : orthogonalPolynomialNorm L (n-1) ≠ 0 :=
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL (n-1) (by omega))).functional_sq_ne_zero
      (hL (n-1+1) (by omega))
  simp only [show n-1+1 = n by omega]
  field_simp [hz n (by omega), hz (n-1) (by omega), hprev]

end NLAlib

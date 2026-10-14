import NLAlib.Polynomial.OrthogonalPolynomials.MeasureOrthogonality

/-!
# The monic three-term recurrence

Multiplication symmetry of a scalar moment functional eliminates all lower basis
coefficients except the two neighboring orders. The proof uses finite Hankel
nondegeneracy and also covers the last finite-support monic polynomial.
Source: Gautschi (2004), Theorem 1.27; atlas `monic-orthogonal-recurrence` and
`formal-orthogonal-polynomials`.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- Pairing a monic orthogonal polynomial with any other monic polynomial of the
same degree gives its squared bilinear norm. -/
theorem IsMonicOrthogonalPolynomial.functional_mul_eq_sq_of_monic
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p q : 𝕜[X]}
    (hp : IsMonicOrthogonalPolynomial L n p) (hq : q.Monic) (hqn : q.natDegree = n) :
    L (p * q) = L (p ^ 2) := by
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have hqd : q.degree = n := by rw [degree_eq_natDegree hq.ne_zero, hqn]
  have hdiff : (p - q).degree < (n : WithBot ℕ) := by
    rw [← hpd]
    exact degree_sub_lt_left (hpd.trans hqd.symm) hp.monic.ne_zero
      (hp.monic.leadingCoeff.trans hq.leadingCoeff.symm)
  have h := hp.orthogonal (p - q) hdiff
  rw [mul_sub, map_sub] at h
  simpa only [pow_two] using (sub_eq_zero.mp h).symm

/-- Monic moment polynomials satisfy the three-term recurrence whenever their
moment systems through the next order are nonsingular. In a positive measure this
includes the terminal polynomial, and the coefficient at order zero is zero.
Source: Gautschi (2004), Theorem 1.27.
atlas: monic-orthogonal-recurrence (partial), formal-orthogonal-polynomials (partial) -/
theorem monicOrthogonalPolynomial_succ_eq
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) :
    monicOrthogonalPolynomial L (n + 1) =
      (X - C (orthogonalRecurrenceAlpha L n)) * monicOrthogonalPolynomial L n -
        C (orthogonalRecurrenceBeta L n) * monicOrthogonalPolynomial L (n - 1) := by
  let P := monicOrthogonalPolynomial L
  let α := orthogonalRecurrenceAlpha L n
  let β := orthogonalRecurrenceBeta L n
  let r := X * P n - P (n + 1) - C α * P n - C β * P (n - 1)
  have hP (k : ℕ) : (P k).Monic := monic_monicOrthogonalPolynomial L k
  have hdeg (k : ℕ) : (P k).degree = k := by
    rw [degree_eq_natDegree (hP k).ne_zero, natDegree_monicOrthogonalPolynomial]
  have hn := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n (by omega))
  have hn1 := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL (n + 1) le_rfl)
  have hnorm : orthogonalPolynomialNorm L n ≠ 0 := hn.functional_sq_ne_zero (hL (n + 1) le_rfl)
  have halpha : α * orthogonalPolynomialNorm L n = L (X * P n ^ 2) := by
    exact div_mul_cancel₀ _ hnorm
  have hdiff : (X * P n - P (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hxdeg : (X * P n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_X, hdeg]
      exact_mod_cast (show 1 + n = n + 1 by omega)
    exact (degree_sub_lt_left (hxdeg.trans (hdeg (n + 1)).symm)
      (monic_X.mul (hP n)).ne_zero
      ((monic_X.mul (hP n)).leadingCoeff.trans (hP (n + 1)).leadingCoeff.symm)).trans_eq hxdeg
  have hαdeg : (C α * P n).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [C_mul']
    exact (degree_smul_le α (P n)).trans_lt (by rw [hdeg]; exact_mod_cast Nat.lt_succ_self n)
  have hβdeg : (C β * P (n - 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [C_mul']
    exact (degree_smul_le β (P (n - 1))).trans_lt (by rw [hdeg]; exact_mod_cast (show n - 1 < n + 1 by omega))
  have hr : r.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt
      (max_lt ((degree_sub_le _ _).trans_lt (max_lt hdiff hαdeg)) hβdeg)
  have hnext (i : ℕ) (hi : i ≤ n) : L (P (n + 1) * P i) = 0 := by
    apply hn1.orthogonal
    rw [hdeg]
    exact_mod_cast (Nat.lt_succ_of_le hi)
  have hpair (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j) :
      L (P i * P j) = 0 :=
    functional_monicOrthogonalPolynomial_mul_eq_zero_of_ne L
      (hL i (by omega)) (hL j (by omega)) hij
  have hrpair (i : ℕ) (hi : i ≤ n) : L (r * P i) = 0 := by
    have hcomm : X * P n * P i = P n * (X * P i) := by ring
    simp only [r, sub_mul, map_sub, mul_assoc, C_mul', smul_mul_assoc, map_smul, smul_eq_mul]
    rw [← mul_assoc X, hnext i hi]
    by_cases hin : i = n
    · subst i
      rw [mul_assoc, ← pow_two]
      change L (X * P n ^ 2) - 0 - α * orthogonalPolynomialNorm L n -
        β * L (P (n - 1) * P n) = 0
      rw [halpha, sub_zero, sub_self, zero_sub]
      by_cases hn0 : n = 0
      · simp [β, orthogonalRecurrenceBeta, hn0]
      · rw [hpair (n - 1) n (by omega) le_rfl (by omega), mul_zero, neg_zero]
    · by_cases hiprev : i = n - 1
      · subst i
        have hnp : 0 < n := by omega
        have hX : (X * P (n - 1)).natDegree = n := by
          rw [natDegree_X_mul (hP _).ne_zero, natDegree_monicOrthogonalPolynomial]
          omega
        have hx := hn.functional_mul_eq_sq_of_monic (monic_X.mul (hP (n - 1))) hX
        rw [hcomm, hx, hpair n (n - 1) le_rfl (by omega) (by omega)]
        rw [← pow_two]
        change orthogonalPolynomialNorm L n - 0 - α * 0 -
          β * orthogonalPolynomialNorm L (n - 1) = 0
        have hpNorm := (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
          (hL (n - 1) (by omega))).functional_sq_ne_zero (hL (n - 1 + 1) (by omega))
        change orthogonalPolynomialNorm L (n - 1) ≠ 0 at hpNorm
        rw [show β = orthogonalPolynomialNorm L n / orthogonalPolynomialNorm L (n - 1) by
          simp only [β, orthogonalRecurrenceBeta, if_neg hnp.ne'], div_mul_cancel₀ _ hpNorm]
        ring
      · have hiLow : i + 1 < n := by omega
        have hx : L (P n * (X * P i)) = 0 := by
          apply hn.orthogonal
          rw [degree_mul, degree_X, hdeg]
          exact_mod_cast (show 1 + i < n by omega)
        rw [hcomm, hx, hpair n i le_rfl hi (fun h => hin h.symm),
          hpair (n - 1) i (by omega) hi (fun h => hiprev h.symm)]
        ring
  have hrzero : r = 0 := by
    apply eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero L
      (hL (n + 1) le_rfl) hr
    intro s hs
    obtain ⟨c, hc⟩ := exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_lt L hs
    rw [← hc, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mul_smul_comm, map_smul, hrpair i (by have := mem_range.mp hi; omega), smul_zero]
  change P (n + 1) = (X - C α) * P n - C β * P (n - 1)
  dsimp only [r] at hrzero
  linear_combination -hrzero

end NLAlib

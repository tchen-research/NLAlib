import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence

/-! # Bounds on monic recurrence coefficients

Compact support gives strict bounds on each diagonal coefficient and a uniform
bound on each positive-order norm-ratio coefficient. The monic coefficient is
the square of a symmetric Jacobi off-diagonal; order zero remains zero.
Source: Gautschi (2004), Theorem 1.28; operator derivations OP12–OP14.
-/

noncomputable section

open Polynomial MeasureTheory Set

namespace NLAlib

/-- A nonnegative affine polynomial times a nonzero degree-`k` polynomial square
has strictly positive integral when the support has at least `k+2` points. -/
theorem integral_eval_mul_sq_pos {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {k : ℕ} (hn : (k + 2 : ℕ∞) ≤ μ.support.encard)
    {p r : ℝ[X]} (hp : p ≠ 0) (hpd : p.degree ≤ k)
    (hr : r ≠ 0) (hrd : r.degree ≤ (1 : ℕ))
    (hpos : ∀ᵐ x ∂μ, 0 ≤ r.eval x) :
    0 < ∫ x, r.eval x * p.eval x ^ 2 ∂μ := by
  have hi : Integrable (fun x => r.eval x * p.eval x ^ 2) μ := by
    convert hμ (r * p ^ 2) using 1
    ext x
    simp
  have hnon : 0 ≤ ∫ x, r.eval x * p.eval x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have hae : (fun x => r.eval x * p.eval x ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (by
      filter_upwards [hpos] with x hx
      exact mul_nonneg hx (sq_nonneg _)) hi).mp hz.symm
  have hs : (∫ x, ((r * p).eval x) ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    have hzero : r.eval x * p.eval x = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · simp [h]
      · simp [sq_eq_zero_iff.mp h]
    simp only [eval_mul, hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]
  have hstrict := integral_sq_eval_pos_of_le_support_encard hn (mul_ne_zero hr hp)
    (p := r * p) (by
      exact (degree_mul_le _ _).trans_lt ((add_le_add hrd hpd).trans_lt (by
        exact_mod_cast (show 1 + k < k + 2 by omega)))) (hμ.integrable_sq (r * p))
  exact hstrict.ne' hs

/-- A monic recurrence diagonal lies strictly between the endpoints of a compact
support interval whenever the measure has more than `k+1` support points.
Source: Gautschi (2004), Theorem 1.28; operator derivations OP12.
atlas: recurrence-coefficient-bounds (partial) -/
theorem orthogonalRecurrenceAlpha_mem_Ioo {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {a b : ℝ} (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {k : ℕ}
    (hn : (k + 2 : ℕ∞) ≤ μ.support.encard) :
    orthogonalRecurrenceAlpha (polynomialIntegral μ hμ) k ∈ Ioo a b := by
  let L := polynomialIntegral μ hμ
  let p := monicOrthogonalPolynomial L k
  let H := orthogonalPolynomialNorm L k
  have hH : 0 < H := orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
    ((by exact_mod_cast (show k + 1 ≤ k + 2 by omega) : (k + 1 : ℕ∞) ≤ k + 2).trans hn)
  have hp : p.Monic := monic_monicOrthogonalPolynomial L k
  have hpd : p.degree ≤ k := by
    rw [degree_eq_natDegree hp.ne_zero, natDegree_monicOrthogonalPolynomial]
  have ha := integral_eval_mul_sq_pos hμ hn hp.ne_zero hpd
    (monic_X_sub_C a).ne_zero (by simp) (by
      filter_upwards [hs] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.1)
  have hb := integral_eval_mul_sq_pos hμ hn hp.ne_zero hpd
    (p := p) (r := C b - X) (by
      intro hz
      have hz' := congrArg (fun s : ℝ[X] => s.coeff 1) hz
      simp at hz') (by
      exact (degree_sub_le _ _).trans (max_le (degree_C_le.trans (by norm_num)) (by simp))) (by
      filter_upwards [hs] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.2)
  have ha' : 0 < L (X * p ^ 2) - a * H := by
    change 0 < L (X * p ^ 2) - a * L (p ^ 2)
    have haL : 0 < L ((X - C a) * p ^ 2) := by
      simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C,
        eval_pow] using ha
    simpa only [sub_mul, map_sub, C_mul', map_smul, smul_eq_mul] using haL
  have hb' : 0 < b * H - L (X * p ^ 2) := by
    change 0 < b * L (p ^ 2) - L (X * p ^ 2)
    have hbL : 0 < L ((C b - X) * p ^ 2) := by
      simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C,
        eval_pow] using hb
    simpa only [sub_mul, map_sub, C_mul', map_smul, smul_eq_mul] using hbL
  change a < L (X * p ^ 2) / H ∧ L (X * p ^ 2) / H < b
  exact ⟨(lt_div_iff₀ hH).mpr (by linarith), (div_lt_iff₀ hH).mpr (by linarith)⟩

/-- Each positive-order monic recurrence coefficient is positive and bounded by
the largest squared endpoint of a compact support interval. It equals the square
of the symmetric Jacobi off-diagonal coefficient.
Source: Gautschi (2004), Theorem 1.28; operator derivations OP13.
atlas: recurrence-coefficient-bounds (partial) -/
theorem orthogonalRecurrenceBeta_pos_and_le {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {a b : ℝ} (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {k : ℕ} (hk : 0 < k)
    (hn : (k + 1 : ℕ∞) ≤ μ.support.encard) :
    0 < orthogonalRecurrenceBeta (polynomialIntegral μ hμ) k ∧
      orthogonalRecurrenceBeta (polynomialIntegral μ hμ) k ≤ max (a ^ 2) (b ^ 2) := by
  let L := polynomialIntegral μ hμ
  let p := monicOrthogonalPolynomial L k
  let r := monicOrthogonalPolynomial L (k - 1)
  let q := X * r
  let H := orthogonalPolynomialNorm L k
  let Hprev := orthogonalPolynomialNorm L (k - 1)
  have hH : 0 < H := orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ hn
  have hHp : 0 < Hprev := orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
    ((by exact_mod_cast (show k - 1 + 1 ≤ k + 1 by omega) :
      (k - 1 + 1 : ℕ∞) ≤ k + 1).trans hn)
  have hp := isMonicOrthogonalPolynomial_polynomialIntegral μ hμ
    ((by exact_mod_cast Nat.le_succ k : (k : ℕ∞) ≤ k + 1).trans hn)
  have hr : r.Monic := monic_monicOrthogonalPolynomial L (k - 1)
  have hqd : q.natDegree = k := by
    rw [natDegree_X_mul hr.ne_zero, natDegree_monicOrthogonalPolynomial]
    omega
  have hpair : L (p * q) = H := hp.functional_mul_eq_sq_of_monic (monic_X.mul hr) hqd
  have hraw : H ≤ L (q ^ 2) := by
    have hnon : 0 ≤ L ((q - p) ^ 2) := by
      change 0 ≤ ∫ x, ((q - p) ^ 2).eval x ∂μ
      simp only [eval_pow]
      exact integral_nonneg (fun x => sq_nonneg _)
    have heq : L ((q - p) ^ 2) = L (q ^ 2) - H := by
      rw [show (q - p) ^ 2 = q ^ 2 - (p * q + p * q) + p ^ 2 by ring,
        map_add, map_sub, map_add, hpair]
      change L (q ^ 2) - (H + H) + H = L (q ^ 2) - H
      ring
    rw [heq] at hnon
    linarith
  have hbound : L (q ^ 2) ≤ max (a ^ 2) (b ^ 2) * Hprev := by
    change (∫ x, (q ^ 2).eval x ∂μ) ≤
      max (a ^ 2) (b ^ 2) * ∫ x, (r ^ 2).eval x ∂μ
    rw [← integral_const_mul]
    apply integral_mono_ae (hμ _) ((hμ _).const_mul _)
    filter_upwards [hs] with x hx
    simp only [eval_pow, q, eval_mul, eval_X, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rcases le_total 0 x with hx0 | hx0
    · have hb0 : 0 ≤ b := hx0.trans hx.2
      exact (sq_le_sq₀ hx0 hb0).mpr hx.2 |>.trans (le_max_right _ _)
    · have ha0 : a ≤ 0 := hx.1.trans hx0
      have hsq : x ^ 2 ≤ a ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (neg_nonneg.mpr hx0)]
      exact hsq.trans (le_max_left _ _)
  change 0 < orthogonalRecurrenceBeta L k ∧ orthogonalRecurrenceBeta L k ≤ _
  rw [orthogonalRecurrenceBeta, if_neg hk.ne']
  exact ⟨div_pos hH hHp, (div_le_iff₀ hHp).mpr (hraw.trans hbound)⟩

end NLAlib

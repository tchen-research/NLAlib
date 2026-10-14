import NLAlib.Krylov.Quadrature.MonicLanczos
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientIdentities

/-! # Monic coefficients of actual signed Lanczos matrices

Consecutive leading traces identify alpha. The actual monic squared-norm products
identify monic beta with the square of each stored signed off-diagonal. The resulting
three-term characteristic recurrence includes the displayed final polynomial, and
the separate grade branch proves its zero terminal norm.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib.LanczosDecomp

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The monic spectral-measure recurrence alpha is the actual Lanczos diagonal.
All stored indices are allowed, including the last diagonal. Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem orthogonalRecurrenceAlpha_spectralMeasure_eq_alpha (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) {j : ℕ} (hj : j < q) :
    orthogonalRecurrenceAlpha
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) j =
        D.alpha j := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  have hL (k : ℕ) (hk : k ≤ j + 1) : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast (show k ≤ krylovGrade A b from (by omega : k ≤ q).trans D.le_krylovGrade)
  have ht (k : ℕ) (hk : k ≤ q) :
      (∑ i ∈ range k, D.alpha i) = -(monicOrthogonalPolynomial L k).nextCoeff := by
    rw [monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (D.restrict hk) hA,
      ← Matrix.trace_eq_neg_charpoly_nextCoeff, D.T_restrict_eq_jacobiMatrix hA hk]
    simp only [Matrix.trace, Matrix.diag, jacobiMatrix, Matrix.of_apply]
    exact (Fin.sum_univ_eq_sum_range D.alpha k).symm
  have hr := orthogonalRecurrenceAlpha_eq_sub_nextCoeff L j hL
  have h0 := ht j hj.le
  have h1 := ht (j + 1) (by omega)
  rw [sum_range_succ] at h1
  change orthogonalRecurrenceAlpha L j = _
  linarith

/-- The monic spectral-measure beta equals the square of the stored signed
Lanczos off-diagonal. Order zero is the shared zero boundary coefficient; no
coupling beyond the decomposition is inferred. Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) {j : ℕ} (hj : j < q) :
    orthogonalRecurrenceBeta
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) j =
        D.beta j ^ 2 := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  have hn (k : ℕ) (hk : k < q) : orthogonalPolynomialNorm L k =
      ‖WithLp.toLp 2 b‖ ^ 2 * ∏ i ∈ Icc 1 k, D.beta i ^ 2 := by
    rw [orthogonalPolynomialNorm, monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (D.restrict hk.le) hA]
    simpa only [L, polynomialIntegral_apply, eval_pow] using
      D.integral_sq_charpoly_restrict_T_eq_norm_sq_mul_prod_beta_sq hA hk
  cases j with
  | zero => simp [orthogonalRecurrenceBeta, beta]
  | succ j =>
    have hH : 0 < orthogonalPolynomialNorm L j := by
      apply orthogonalPolynomialNorm_pos_of_lt_support_encard
      rw [support_encard_spectralMeasure_eq_krylovGrade]
      exact_mod_cast (show j + 1 ≤ krylovGrade A b from (by omega : j + 1 ≤ q).trans D.le_krylovGrade)
    have h1 := hn (j + 1) hj
    have h0 := hn j (by omega)
    rw [prod_Icc_succ_top (by omega : 1 ≤ j + 1), ← mul_assoc, ← h0] at h1
    rw [orthogonalRecurrenceBeta, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, h1]
    exact mul_div_cancel_left₀ _ hH.ne'

/-- Every actual leading monic characteristic polynomial satisfies the three-term
recurrence with the actual diagonal and squared signed off-diagonal. The final
displayed characteristic polynomial is included. Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem charpoly_restrict_T_succ_eq (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {j : ℕ} (hj : j + 1 ≤ q) :
    (LanczosDecomp.T (D.restrict hj)).charpoly =
      (X - C (D.alpha j)) * (LanczosDecomp.T (D.restrict (by omega : j ≤ q))).charpoly -
        C (D.beta j ^ 2) * (LanczosDecomp.T (D.restrict (by omega : j - 1 ≤ q))).charpoly := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  have hL (k : ℕ) (hk : k ≤ j + 1) : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast ((hk.trans hj).trans D.le_krylovGrade)
  have hr := monicOrthogonalPolynomial_succ_eq L j hL
  rw [D.orthogonalRecurrenceAlpha_spectralMeasure_eq_alpha hA (by omega),
    D.orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq hA (by omega),
    monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (D.restrict hj) hA,
    monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (D.restrict (by omega : j ≤ q)) hA,
    monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (D.restrict (by omega : j - 1 ≤ q)) hA] at hr
  exact hr

/-- At exact Krylov grade the actual final monic characteristic polynomial has
zero squared integral norm. It is not normalized into a final basis polynomial.
Source: operator derivations, terminal convention following (OF11).
atlas: monic-orthogonal-recurrence (partial) -/
theorem integral_sq_charpoly_T_eq_zero_of_eq_grade (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : q = krylovGrade A b) :
    (∫ x, D.T.charpoly.eval x ^ 2 ∂spectralMeasure hA b) = 0 := by
  let μ := spectralMeasure hA b
  let hμ := hasPolynomialMoments_spectralMeasure hA b
  have he : μ.support.encard = (q : ℕ∞) := by rw [support_encard_spectralMeasure_eq_krylovGrade, ← hq]
  have hfinite := Set.finite_of_encard_eq_coe he
  have hcard : hfinite.toFinset.card = q := by exact_mod_cast (hfinite.encard_eq_coe_toFinset_card.symm.trans he)
  have hz := orthogonalPolynomialNorm_eq_zero_of_finite_support μ hμ hfinite
  rw [hcard] at hz
  rw [orthogonalPolynomialNorm, D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA] at hz
  simpa only [μ, polynomialIntegral_apply, eval_pow] using hz

/-- At exact grade the final monic beta is the squared zero terminal Lanczos
coupling. It is the zero norm ratio, and does not create a normalized final vector.
The zero-grade boundary is included. Source: terminal convention following (OF11).
atlas: monic-orthogonal-recurrence (partial) -/
theorem orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq_of_eq_grade
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) (hq : q = krylovGrade A b) :
    orthogonalRecurrenceBeta
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q =
        D.beta q ^ 2 := by
  have hb : D.beta q = 0 := by simp [beta]
  rw [hb, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  by_cases hq0 : q = 0
  · simp [hq0, orthogonalRecurrenceBeta]
  rw [orthogonalRecurrenceBeta, if_neg hq0, orthogonalPolynomialNorm,
    D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA]
  simp only [polynomialIntegral_apply, eval_pow,
    D.integral_sq_charpoly_T_eq_zero_of_eq_grade hA hq, zero_div]

end NLAlib.LanczosDecomp

import NLAlib.Matrix.Norms.SchattenEndpoints
import NLAlib.ForMathlib.Analysis.FinitePowerSums
/-!
# Sharp Schatten exponent comparisons

The support is the actual matrix rank. Extended reciprocal exponents include
infinity exactly, and all comparisons cover rank zero and empty shapes.
Source: Bhatia (1997), §IV.2; matrix toolkit derivations, (12).
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Every positive-exponent Schatten power sum uses exactly the actual rank
prefix; zero rank yields an empty sum.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem schattenNorm_eq_sum_rank_rpow (A : Matrix m n ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = (∑ i ∈ Finset.range A.rank, singularValues A i ^ p) ^ (1 / p) := by
  unfold schattenNorm
  congr 1
  symm
  have hr : A.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    le_min A.rank_le_card_height A.rank_le_card_width
  apply Finset.sum_subset (Finset.range_subset_range.mpr hr)
  intro i _ hi
  rw [singularValues_eq_zero_of_rank_le A (by
    simpa only [Finset.mem_range, not_lt] using hi), Real.zero_rpow hp.ne']

/-- Every positive-exponent Schatten norm dominates the spectral norm,
including the zero and empty matrix cases.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem specNorm_le_schattenNorm (A : Matrix m n ℝ) {p : ℝ} (hp : 0 < p) :
    specNorm A ≤ schattenNorm A p := by
  have hfirst : singularValues A 0 = specNorm A := by
    simpa only [kyFanNorm, Finset.sum_range_one, singularValues_eq_linearMap] using
      kyFanNorm_one_eq_specNorm A
  have hsum : specNorm A ^ p ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i ^ p := by
    by_cases hN : 0 < min (Fintype.card m) (Fintype.card n)
    · rw [← hfirst]
      exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (singularValues_nonneg _ i) p)
        (Finset.mem_range.mpr hN)
    · have hs : specNorm A = 0 := by
        rw [← hfirst]
        exact singularValues_eq_zero_of_min_le A (by omega)
      rw [hs, Real.zero_rpow hp.ne']
      exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (singularValues_nonneg _ i) p)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (specNorm_nonneg A) p) hsum
    (one_div_nonneg.mpr hp.le)
  rw [one_div, Real.rpow_rpow_inv (specNorm_nonneg A) hp.ne'] at h
  simpa only [schattenNorm, one_div] using h

omit [DecidableEq m] in
/-- Finite Schatten norms decrease with their positive real exponent.
The source norm-exponent range is included as a special case.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem schattenNorm_le_schattenNorm_of_le (A : Matrix m n ℝ) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) : schattenNorm A q ≤ schattenNorm A p :=
  sum_rpow_root_le_sum_rpow_root _ _ (fun i _ => singularValues_nonneg _ i) hp hpq

omit [DecidableEq m] in
/-- The sharp finite-exponent comparison uses the actual matrix rank, with
coefficient `rank(A)^(1/p - 1/q)`. The zero rank is covered without division.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem schattenNorm_le_rank_rpow_mul_schattenNorm (A : Matrix m n ℝ) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    schattenNorm A p ≤ (A.rank : ℝ) ^ (1 / p - 1 / q) * schattenNorm A q := by
  rw [schattenNorm_eq_sum_rank_rpow A hp,
    schattenNorm_eq_sum_rank_rpow A (hp.trans_le hpq)]
  simpa only [Finset.card_range] using sum_rpow_root_le_card_rpow_mul (Finset.range A.rank)
    (singularValues A) (fun i _ => singularValues_nonneg _ i) hp hpq

/-- The sharp finite-to-infinite exponent bound uses the actual rank,
including rank zero and empty matrix shapes.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem schattenNorm_le_rank_rpow_mul_specNorm (A : Matrix m n ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ≤ (A.rank : ℝ) ^ (1 / p) * specNorm A := by
  rw [schattenNorm_eq_sum_rank_rpow A hp]
  have hsum : (∑ i ∈ Finset.range A.rank, singularValues A i ^ p) ≤
      (A.rank : ℝ) * specNorm A ^ p := by
    calc
      _ ≤ ∑ _i ∈ Finset.range A.rank, specNorm A ^ p :=
        Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (singularValues_nonneg _ i)
          (singularValues_le_specNorm A i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg _ i) p) hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg A.rank) (Real.rpow_nonneg (specNorm_nonneg A) p),
    one_div, Real.rpow_rpow_inv (specNorm_nonneg A) hp.ne'] at h
  simpa only [one_div] using h

/-- Extended Schatten norms decrease for `1 ≤ p ≤ q ≤ ∞`.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem schattenNormExtended_le_of_le (A : Matrix m n ℝ) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) : schattenNormExtended A q ≤ schattenNormExtended A p := by
  by_cases hpTop : p = ∞
  · subst p
    have hq : q = ∞ := top_le_iff.mp hpq
    subst q
    exact le_rfl
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hp)) hpTop
    by_cases hqTop : q = ∞
    · subst q
      rw [schattenNormExtended_top, schattenNormExtended_eq_of_ne_top _ hpTop]
      exact specNorm_le_schattenNorm A hp0
    · rw [schattenNormExtended_eq_of_ne_top _ hpTop, schattenNormExtended_eq_of_ne_top _ hqTop]
      exact schattenNorm_le_schattenNorm_of_le A hp0 (ENNReal.toReal_mono hqTop hpq)

/-- The sharp actual-rank comparison for all `1 ≤ p ≤ q ≤ ∞`, using
extended reciprocals so that `1/∞ = 0`. Rank zero obeys the same formula.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem schattenNormExtended_le_rank_rpow_mul (A : Matrix m n ℝ) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) :
    schattenNormExtended A p ≤ (A.rank : ℝ) ^ (p⁻¹.toReal - q⁻¹.toReal) * schattenNormExtended A q := by
  by_cases hpTop : p = ∞
  · subst p
    have hq : q = ∞ := top_le_iff.mp hpq
    subst q
    simp
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hp)) hpTop
    by_cases hqTop : q = ∞
    · subst q
      simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, ENNReal.toReal_inv,
        schattenNormExtended_top]
      rw [schattenNormExtended_eq_of_ne_top _ hpTop]
      simpa only [one_div] using schattenNorm_le_rank_rpow_mul_specNorm A hp0
    · rw [schattenNormExtended_eq_of_ne_top _ hpTop, schattenNormExtended_eq_of_ne_top _ hqTop]
      simpa only [ENNReal.toReal_inv, one_div] using
        schattenNorm_le_rank_rpow_mul_schattenNorm A hp0 (ENNReal.toReal_mono hqTop hpq)

end NLAlib

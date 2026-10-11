import NLAlib.LowRank.ComplexCholeskyPivot
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite adaptive complex Cholesky histories

Every finite-time RPCholesky expectation is a finite weighted sum over pivot
histories. The transition identity supplies conditional averaging without regular
conditional probabilities or a random eigenbasis.
Source: manuscript `sa:rpcholesky`; CETW (2025), and the complex audit Part VII.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The residual after a chronological finite pivot history.
Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky iteration. -/
def complexCholeskyResidualHistory (A : Matrix n n ℂ) : (t : ℕ) → (Fin t → n) → Matrix n n ℂ
  | 0, _ => A
  | t + 1, h => complexCholeskyResidualStep
      (complexCholeskyResidualHistory A t (Fin.init h)) (h (Fin.last t))

/-- The probability weight of a finite adaptive pivot history is the product of its
transition probabilities. Source: manuscript `sa:rpcholesky`, finite-history law. -/
def complexCholeskyHistoryWeight (A : Matrix n n ℂ) : (t : ℕ) → (Fin t → n) → ℝ
  | 0, _ => 1
  | t + 1, h => complexCholeskyHistoryWeight A t (Fin.init h) *
      complexCholeskyPivotProbability (complexCholeskyResidualHistory A t (Fin.init h)) (h (Fin.last t))

/-- Expected residual trace is the finite weighted sum over adaptive pivot histories.
Source: manuscript `sa:rpcholesky`, `u_t = E tr R_t`. -/
def complexCholeskyExpectedTrace (A : Matrix n n ℂ) (t : ℕ) : ℝ :=
  ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h * (complexCholeskyResidualHistory A t h).trace.re

/-- Every finite-history residual remains positive semidefinite.
Source: manuscript `sa:rp-one-step`; CETW (2025), PSD invariant. -/
theorem posSemidef_complexCholeskyResidualHistory {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) : (complexCholeskyResidualHistory A t h).PosSemidef := by
  induction t with
  | zero => exact hA
  | succ t ih => exact posSemidef_complexCholeskyResidualStep (ih (Fin.init h)) _

/-- Every finite-history Cholesky residual is bounded above by its original matrix.
Source: manuscript `sa:rp-one-step`; CETW (2025), PSD order invariant. -/
theorem posSemidef_sub_complexCholeskyResidualHistory {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) : (A - complexCholeskyResidualHistory A t h).PosSemidef := by
  induction t with
  | zero => simpa only [complexCholeskyResidualHistory, sub_self] using (Matrix.PosSemidef.zero (n := n) (R := ℂ))
  | succ t ih =>
    have h := (ih (Fin.init h)).add
      (posSemidef_sub_complexCholeskyResidualStep (posSemidef_complexCholeskyResidualHistory hA t (Fin.init h))
        (h (Fin.last t)))
    convert h using 1
    dsimp only [complexCholeskyResidualHistory]
    abel

/-- Finite adaptive-history weights are nonnegative for positive semidefinite input.
Source: manuscript `sa:rpcholesky`, finite probability law. -/
theorem complexCholeskyHistoryWeight_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) : 0 ≤ complexCholeskyHistoryWeight A t h := by
  induction t with
  | zero => exact zero_le_one
  | succ t ih =>
    exact mul_nonneg (ih (Fin.init h))
      (complexCholeskyPivotProbability_nonneg (posSemidef_complexCholeskyResidualHistory hA t (Fin.init h)) _)

omit [DecidableEq n] in
/-- Finite adaptive expectation at the next time is the current weighted average
of the finite transition expectations. Source: manuscript `sa:rpcholesky`;
finite conditional averaging, with no regular conditional probability assumption. -/
theorem sum_complexCholeskyHistoryWeight_mul_succ (A : Matrix n n ℂ) (t : ℕ)
    (f : Matrix n n ℂ → ℝ) :
    (∑ h : Fin (t + 1) → n, complexCholeskyHistoryWeight A (t + 1) h *
      f (complexCholeskyResidualHistory A (t + 1) h)) =
      ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h *
        ∑ i : n, complexCholeskyPivotProbability (complexCholeskyResidualHistory A t h) i *
          f (complexCholeskyResidualStep (complexCholeskyResidualHistory A t h) i) := by
  calc (∑ h : Fin (t + 1) → n, complexCholeskyHistoryWeight A (t + 1) h *
      f (complexCholeskyResidualHistory A (t + 1) h)) =
      ∑ z : n × (Fin t → n), complexCholeskyHistoryWeight A t z.2 *
        complexCholeskyPivotProbability (complexCholeskyResidualHistory A t z.2) z.1 *
          f (complexCholeskyResidualStep (complexCholeskyResidualHistory A t z.2) z.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) => n)).symm _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type_right]
      simp only [mul_assoc, Finset.mul_sum]

omit [DecidableEq n] in
/-- The adaptive-history weights sum to one at every time, including after absorption.
Source: manuscript `sa:rpcholesky`, finite probability histories. -/
theorem sum_complexCholeskyHistoryWeight [Nonempty n] (A : Matrix n n ℂ) (t : ℕ) :
    ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h = 1 := by
  induction t with
  | zero => simp [complexCholeskyHistoryWeight]
  | succ t ih =>
    have h := sum_complexCholeskyHistoryWeight_mul_succ A t (fun _ => 1)
    simpa only [mul_one, sum_complexCholeskyPivotProbability, mul_one, ih] using h

omit [DecidableEq n] in
/-- The expected trace starts at the original input trace.
Source: manuscript `sa:rpcholesky`, initial trace `u_0 = tr A`. -/
@[simp] theorem complexCholeskyExpectedTrace_zero (A : Matrix n n ℂ) :
    complexCholeskyExpectedTrace A 0 = A.trace.re := by
  simp [complexCholeskyExpectedTrace, complexCholeskyHistoryWeight, complexCholeskyResidualHistory]

/-- Every expected Cholesky residual trace is nonnegative.
Source: manuscript `sa:rpcholesky`, bounded finite moments. -/
theorem complexCholeskyExpectedTrace_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (t : ℕ) :
    0 ≤ complexCholeskyExpectedTrace A t := by
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg (complexCholeskyHistoryWeight_nonneg hA t h)
  exact re_trace_nonneg_of_complex_posSemidef (posSemidef_complexCholeskyResidualHistory hA t h)

/-- The expected trace is nonincreasing along the actual finite-history process.
Source: manuscript `sa:rpcholesky`, bounded finite moments and monotonicity. -/
theorem complexCholeskyExpectedTrace_antitone [Nonempty n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : Antitone (complexCholeskyExpectedTrace A) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [complexCholeskyExpectedTrace,
    sum_complexCholeskyHistoryWeight_mul_succ A t (fun R => R.trace.re)]
  change _ ≤ ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h * (complexCholeskyResidualHistory A t h).trace.re
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (complexCholeskyHistoryWeight_nonneg hA t h)
  let R := complexCholeskyResidualHistory A t h
  have hR : R.PosSemidef := posSemidef_complexCholeskyResidualHistory hA t h
  calc
    (∑ i, complexCholeskyPivotProbability R i * (complexCholeskyResidualStep R i).trace.re) ≤
        ∑ i, complexCholeskyPivotProbability R i * R.trace.re := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (complexCholeskyPivotProbability_nonneg hR i)
      have hn : 0 ≤ (R - complexCholeskyResidualStep R i).trace.re :=
        re_trace_nonneg_of_complex_posSemidef (posSemidef_sub_complexCholeskyResidualStep hR i)
      rw [Matrix.trace_sub, Complex.sub_re] at hn
      linarith
    _ = R.trace.re := by rw [← Finset.sum_mul, sum_complexCholeskyPivotProbability, one_mul]

/-- The one-step trace mean also holds at the absorbing zero state, using totalized
division by zero. Source: manuscript `sa:rp-recursion`, absorbing-zero extension. -/
theorem sum_complexCholeskyPivotProbability_mul_trace_step_eq_all [Nonempty n]
    {R : Matrix n n ℂ} (hR : R.PosSemidef) :
    (∑ i, complexCholeskyPivotProbability R i * (complexCholeskyResidualStep R i).trace.re) =
      R.trace.re - (R * R).trace.re / R.trace.re :=
  sum_complexCholeskyPivotProbability_mul_re_trace_step_eq hR

/-- The actual adaptive expected trace obeys the exact finite one-step averaging
formula before applying the scalar tail drift. Source: manuscript `sa:rp-recursion`. -/
theorem complexCholeskyExpectedTrace_succ_eq [Nonempty n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (t : ℕ) :
    complexCholeskyExpectedTrace A (t + 1) =
      ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h *
        ((complexCholeskyResidualHistory A t h).trace.re -
          (complexCholeskyResidualHistory A t h * complexCholeskyResidualHistory A t h).trace.re /
            (complexCholeskyResidualHistory A t h).trace.re) := by
  rw [complexCholeskyExpectedTrace,
    sum_complexCholeskyHistoryWeight_mul_succ A t (fun R => R.trace.re)]
  apply Finset.sum_congr rfl
  intro h _
  rw [sum_complexCholeskyPivotProbability_mul_trace_step_eq_all
    (posSemidef_complexCholeskyResidualHistory hA t h)]

/-- Every positive-probability adaptive history has exhausted one residual rank per
nonzero pivot. Source: manuscript `sa:rp-rank`; CETW (2025), exact-rank exhaustion.
The zero state is absorbing, so subtraction is totalized on natural ranks. -/
theorem rank_complexCholeskyResidualHistory_le_sub {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) (hw : 0 < complexCholeskyHistoryWeight A t h) :
    (complexCholeskyResidualHistory A t h).rank ≤ A.rank - t := by
  induction t with
  | zero => simp only [complexCholeskyResidualHistory, Nat.sub_zero, le_refl]
  | succ t ih =>
    let R := complexCholeskyResidualHistory A t (Fin.init h)
    have hR : R.PosSemidef := posSemidef_complexCholeskyResidualHistory hA t (Fin.init h)
    have hW0 := complexCholeskyHistoryWeight_nonneg hA t (Fin.init h)
    have hP0 := complexCholeskyPivotProbability_nonneg hR (h (Fin.last t))
    change 0 < complexCholeskyHistoryWeight A t (Fin.init h) * complexCholeskyPivotProbability R (h (Fin.last t)) at hw
    have hW : 0 < complexCholeskyHistoryWeight A t (Fin.init h) := by
      by_contra hn
      have he : complexCholeskyHistoryWeight A t (Fin.init h) = 0 :=
        le_antisymm (not_lt.mp hn) hW0
      rw [he, zero_mul] at hw
      linarith
    have hP : 0 < complexCholeskyPivotProbability R (h (Fin.last t)) := by
      by_contra hn
      have he : complexCholeskyPivotProbability R (h (Fin.last t)) = 0 :=
        le_antisymm (not_lt.mp hn) hP0
      rw [he, mul_zero] at hw
      linarith
    have hprev := ih (Fin.init h) hW
    by_cases hz : R = 0
    · change (complexCholeskyResidualStep R _).rank ≤ _
      rw [hz, complexCholeskyResidualStep_zero, Matrix.rank_zero]
      exact Nat.zero_le _
    · have htr : R.trace.re ≠ 0 := by
        intro hzero
        exact hz ((re_trace_eq_zero_iff_of_complex_posSemidef hR).mp hzero)
      have hdiag : R (h (Fin.last t)) (h (Fin.last t)) ≠ 0 := by
        intro hzero
        simp only [complexCholeskyPivotProbability, if_neg htr, hzero, Complex.zero_re,
          zero_div] at hP
        linarith
      have hdrop := rank_complexCholeskyResidualStep_lt hdiag
      change (complexCholeskyResidualStep R _).rank ≤ _
      change R.rank ≤ A.rank - t at hprev
      omega

/-- Every positive-probability pivot history is exact once its length reaches the
input rank. Source: manuscript `sa:rp-rank`; CETW (2025), rank-zero termination.
atlas: rpcholesky (partial) -/
theorem complexCholeskyResidualHistory_eq_zero_of_rank_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℕ} (ht : A.rank ≤ t) (h : Fin t → n) (hw : 0 < complexCholeskyHistoryWeight A t h) :
    complexCholeskyResidualHistory A t h = 0 := by
  apply eq_zero_of_complex_matrix_rank_eq_zero
  have hr := rank_complexCholeskyResidualHistory_le_sub hA t h hw
  rw [Nat.sub_eq_zero_of_le ht] at hr
  exact Nat.eq_zero_of_le_zero hr

/-- The expected trace is exactly zero after at most the input rank positive pivots.
Source: manuscript `sa:rp-rank` and `sa:rp-theorem`, zero-tail branch.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_eq_zero_of_rank_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℕ} (ht : A.rank ≤ t) : complexCholeskyExpectedTrace A t = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  by_cases hw : complexCholeskyHistoryWeight A t h = 0
  · rw [hw, zero_mul]
  · have hp : 0 < complexCholeskyHistoryWeight A t h :=
      (complexCholeskyHistoryWeight_nonneg hA t h).lt_of_ne (Ne.symm hw)
    rw [complexCholeskyResidualHistory_eq_zero_of_rank_le hA ht h hp, Matrix.trace_zero,
      Complex.zero_re, mul_zero]

end NLAlib

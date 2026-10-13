import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.HasLaw
import NLAlib.LowRank.Cholesky.CholeskyPivot
import NLAlib.LowRank.Cholesky.PartialCholesky

/-!
# Finite adaptive Cholesky histories

`choleskyHistoryLaw` is the canonical adaptive law;
`integral_trace_choleskyHistoryLaw` computes its trace expectation.
The finite weighted formula sums over pivot
histories `h : Fin t → n`, whose residuals are `partialCholeskyResidual A h`. The transition
identity supplies conditional averaging without regular conditional probabilities or a random
eigenbasis.
Source: manuscript `sa:rpcholesky`; CETW (2025).
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The probability weight of a finite adaptive pivot history is the product of its
transition probabilities. Source: manuscript `sa:rpcholesky`, finite-history law. -/
def choleskyHistoryWeight (A : Matrix n n ℝ) : (t : ℕ) → (Fin t → n) → ℝ
  | 0, _ => 1
  | t + 1, h => choleskyHistoryWeight A t (Fin.init h) *
      choleskyPivotProbability (partialCholeskyResidual A (Fin.init h)) (h (Fin.last t))

/-- Expected residual trace is the finite weighted sum over adaptive pivot histories.
Source: manuscript `sa:rpcholesky`, `u_t = E tr R_t`. -/
def choleskyExpectedTrace (A : Matrix n n ℝ) (t : ℕ) : ℝ :=
  ∑ h : Fin t → n, choleskyHistoryWeight A t h * (partialCholeskyResidual A h).trace

/-- Finite adaptive-history weights are nonnegative for positive semidefinite input.
Source: manuscript `sa:rpcholesky`, finite probability law. -/
theorem choleskyHistoryWeight_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) : 0 ≤ choleskyHistoryWeight A t h := by
  induction t with
  | zero => exact zero_le_one
  | succ t ih =>
    exact mul_nonneg (ih (Fin.init h))
      (choleskyPivotProbability_nonneg (posSemidef_partialCholeskyResidual hA (Fin.init h)) _)

omit [DecidableEq n] in
/-- Finite adaptive expectation at the next time is the current weighted average
of the finite transition expectations. Source: manuscript `sa:rpcholesky`;
finite conditional averaging, with no regular conditional probability assumption. -/
theorem sum_choleskyHistoryWeight_mul_succ (A : Matrix n n ℝ) (t : ℕ)
    (f : Matrix n n ℝ → ℝ) :
    (∑ h : Fin (t + 1) → n, choleskyHistoryWeight A (t + 1) h *
      f (partialCholeskyResidual A h)) =
      ∑ h : Fin t → n, choleskyHistoryWeight A t h *
        ∑ i : n, choleskyPivotProbability (partialCholeskyResidual A h) i *
          f (eliminationStep (partialCholeskyResidual A h) i) := by
  calc (∑ h : Fin (t + 1) → n, choleskyHistoryWeight A (t + 1) h *
      f (partialCholeskyResidual A h)) =
      ∑ z : n × (Fin t → n), choleskyHistoryWeight A t z.2 *
        choleskyPivotProbability (partialCholeskyResidual A z.2) z.1 *
          f (eliminationStep (partialCholeskyResidual A z.2) z.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) => n)).symm _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type_right]
      simp only [mul_assoc, Finset.mul_sum]

omit [DecidableEq n] in
/-- The adaptive-history weights sum to one at every time, including after absorption.
Source: manuscript `sa:rpcholesky`, finite probability histories. -/
theorem sum_choleskyHistoryWeight [Nonempty n] (A : Matrix n n ℝ) (t : ℕ) :
    ∑ h : Fin t → n, choleskyHistoryWeight A t h = 1 := by
  induction t with
  | zero => simp [choleskyHistoryWeight]
  | succ t ih =>
    have h := sum_choleskyHistoryWeight_mul_succ A t (fun _ => 1)
    simpa only [mul_one, sum_choleskyPivotProbability, mul_one, ih] using h

omit [DecidableEq n] in
/-- The expected trace starts at the original input trace.
Source: manuscript `sa:rpcholesky`, initial trace `u_0 = tr A`. -/
@[simp] theorem choleskyExpectedTrace_zero (A : Matrix n n ℝ) :
    choleskyExpectedTrace A 0 = A.trace := by
  simp [choleskyExpectedTrace, choleskyHistoryWeight, partialCholeskyResidual]

/-- Every expected Cholesky residual trace is nonnegative.
Source: manuscript `sa:rpcholesky`, bounded finite moments. -/
theorem choleskyExpectedTrace_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (t : ℕ) :
    0 ≤ choleskyExpectedTrace A t := by
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg (choleskyHistoryWeight_nonneg hA t h)
  exact Finset.sum_nonneg fun j _ => (posSemidef_partialCholeskyResidual hA h).diag_nonneg

/-- The expected trace is nonincreasing along the actual finite-history process.
Source: manuscript `sa:rpcholesky`, bounded finite moments and monotonicity. -/
theorem choleskyExpectedTrace_antitone [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : Antitone (choleskyExpectedTrace A) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [choleskyExpectedTrace, sum_choleskyHistoryWeight_mul_succ]
  change _ ≤ ∑ h : Fin t → n, choleskyHistoryWeight A t h * (partialCholeskyResidual A h).trace
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (choleskyHistoryWeight_nonneg hA t h)
  let R := partialCholeskyResidual A h
  have hR : R.PosSemidef := posSemidef_partialCholeskyResidual hA h
  calc
    (∑ i, choleskyPivotProbability R i * (eliminationStep R i).trace) ≤
        ∑ i, choleskyPivotProbability R i * R.trace := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (choleskyPivotProbability_nonneg hR i)
      have hn : 0 ≤ (R - eliminationStep R i).trace :=
        Finset.sum_nonneg fun j _ => (Matrix.le_iff.mp (eliminationStep_le hR i)).diag_nonneg
      rw [Matrix.trace_sub] at hn
      linarith
    _ = R.trace := by rw [← Finset.sum_mul, sum_choleskyPivotProbability, one_mul]

/-- The actual adaptive expected trace obeys the exact finite one-step averaging
formula before applying the scalar tail drift. Source: manuscript `sa:rp-recursion`. -/
theorem choleskyExpectedTrace_succ_eq [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (t : ℕ) :
    choleskyExpectedTrace A (t + 1) =
      ∑ h : Fin t → n, choleskyHistoryWeight A t h *
        ((partialCholeskyResidual A h).trace -
          (partialCholeskyResidual A h * partialCholeskyResidual A h).trace /
            (partialCholeskyResidual A h).trace) := by
  rw [choleskyExpectedTrace, sum_choleskyHistoryWeight_mul_succ]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (fun x => choleskyHistoryWeight A t h * x)
    (sum_choleskyPivotProbability_mul_re_trace_eliminationStep_eq
      (posSemidef_partialCholeskyResidual hA h))

/-- Every positive-probability adaptive history has exhausted one residual rank per
nonzero pivot. Source: manuscript `sa:rp-rank`; CETW (2025), exact-rank exhaustion.
The zero state is absorbing, so subtraction is totalized on natural ranks. -/
theorem rank_partialCholeskyResidual_le_sub {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (t : ℕ) (h : Fin t → n) (hw : 0 < choleskyHistoryWeight A t h) :
    (partialCholeskyResidual A h).rank ≤ A.rank - t := by
  induction t with
  | zero => simp only [partialCholeskyResidual, Nat.sub_zero, le_refl]
  | succ t ih =>
    let R := partialCholeskyResidual A (Fin.init h)
    have hR : R.PosSemidef := posSemidef_partialCholeskyResidual hA (Fin.init h)
    have hW0 := choleskyHistoryWeight_nonneg hA t (Fin.init h)
    have hP0 := choleskyPivotProbability_nonneg hR (h (Fin.last t))
    change 0 < choleskyHistoryWeight A t (Fin.init h) *
      choleskyPivotProbability R (h (Fin.last t)) at hw
    have hW : 0 < choleskyHistoryWeight A t (Fin.init h) := by
      by_contra hn
      have he : choleskyHistoryWeight A t (Fin.init h) = 0 :=
        le_antisymm (not_lt.mp hn) hW0
      rw [he, zero_mul] at hw
      linarith
    have hP : 0 < choleskyPivotProbability R (h (Fin.last t)) := by
      by_contra hn
      have he : choleskyPivotProbability R (h (Fin.last t)) = 0 :=
        le_antisymm (not_lt.mp hn) hP0
      rw [he, mul_zero] at hw
      linarith
    have hprev := ih (Fin.init h) hW
    by_cases hz : R = 0
    · change (eliminationStep R _).rank ≤ _
      rw [hz, eliminationStep_zero, Matrix.rank_zero]
      exact Nat.zero_le _
    · have htr : R.trace ≠ 0 := by
        intro hzero
        exact hz (hR.trace_eq_zero_iff.mp hzero)
      have hdiag : R (h (Fin.last t)) (h (Fin.last t)) ≠ 0 := by
        intro hzero
        simp only [choleskyPivotProbability, RCLike.re_to_real, if_neg htr, hzero, zero_div] at hP
        linarith
      have hdrop := rank_eliminationStep_lt hdiag
      change (eliminationStep R _).rank ≤ _
      change R.rank ≤ A.rank - t at hprev
      omega

/-- Every positive-probability pivot history is exact once its length reaches the
input rank. Source: manuscript `sa:rp-rank`; CETW (2025), rank-zero termination.
atlas: rpcholesky (partial) -/
theorem partialCholeskyResidual_eq_zero_of_rank_le {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {t : ℕ} (ht : A.rank ≤ t) (h : Fin t → n) (hw : 0 < choleskyHistoryWeight A t h) :
    partialCholeskyResidual A h = 0 := by
  apply eq_zero_of_matrix_rank_eq_zero
  have hr := rank_partialCholeskyResidual_le_sub hA t h hw
  rw [Nat.sub_eq_zero_of_le ht] at hr
  exact Nat.eq_zero_of_le_zero hr

/-- The expected trace is exactly zero after at most the input rank positive pivots.
Source: manuscript `sa:rp-rank` and `sa:rp-theorem`, zero-tail branch.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_eq_zero_of_rank_le {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {t : ℕ} (ht : A.rank ≤ t) : choleskyExpectedTrace A t = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  by_cases hw : choleskyHistoryWeight A t h = 0
  · rw [hw, zero_mul]
  · have hp : 0 < choleskyHistoryWeight A t h :=
      (choleskyHistoryWeight_nonneg hA t h).lt_of_ne (Ne.symm hw)
    rw [partialCholeskyResidual_eq_zero_of_rank_le hA ht h hp, Matrix.trace_zero, mul_zero]

/-- The probability mass function of the adaptive pivot history.
Source: CETW (2025), RPCholesky pivot rule. -/
def choleskyHistoryPMF [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (t : ℕ) : PMF (Fin t → n) := by
  classical
  refine PMF.ofFintype (fun h => ENNReal.ofReal (choleskyHistoryWeight A t h)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => choleskyHistoryWeight_nonneg hA t h),
    sum_choleskyHistoryWeight A t]
  simp

/-- The measure of adaptive pivot histories, including absorbed zero residuals.
Source: CETW (2025), RPCholesky pivot rule. -/
def choleskyHistoryLaw [Nonempty n] [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) :
    MeasureTheory.Measure (Fin t → n) := (choleskyHistoryPMF A hA t).toMeasure

/-- The adaptive history law is a probability measure. -/
instance choleskyHistoryLaw_isProbabilityMeasure [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) :
    MeasureTheory.IsProbabilityMeasure (choleskyHistoryLaw A hA t) := by
  unfold choleskyHistoryLaw
  infer_instance

/-- Integration over adaptive histories is their transition-weighted sum.
Source: CETW (2025), finite conditional averaging. -/
theorem integral_choleskyHistoryLaw [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) (f : (Fin t → n) → ℝ) :
    (∫ h, f h ∂choleskyHistoryLaw A hA t) =
      ∑ h, choleskyHistoryWeight A t h * f h := by
  classical
  rw [choleskyHistoryLaw, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro h _
  change (ENNReal.ofReal (choleskyHistoryWeight A t h)).toReal • f h = _
  rw [ENNReal.toReal_ofReal (choleskyHistoryWeight_nonneg hA t h)]
  rfl

/-- The weighted trace formula computes the residual-trace expectation.
Source: CETW (2025), RPCholesky trace potential. -/
theorem integral_trace_choleskyHistoryLaw [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) :
    (∫ h, (partialCholeskyResidual A h).trace ∂choleskyHistoryLaw A hA t) =
      choleskyExpectedTrace A t := integral_choleskyHistoryLaw A hA t _

/-- A random history with the adaptive law has the same trace expectation.
Source: CETW (2025), RPCholesky trace potential. -/
theorem integral_trace_choleskyHistoryLaw_of_hasLaw [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) {H : Ω → Fin t → n}
    (hH : ProbabilityTheory.HasLaw H (choleskyHistoryLaw A hA t) μ) :
    (∫ ω, (partialCholeskyResidual A (H ω)).trace ∂μ) =
      choleskyExpectedTrace A t := by
  rw [← integral_trace_choleskyHistoryLaw A hA t]
  exact hH.integral_comp (Measurable.aestronglyMeasurable (measurable_of_finite (fun h : Fin t → n => (partialCholeskyResidual A h).trace)))

/-- Each adaptive history has its product of conditional pivot probabilities as mass.
Source: CETW (2025), RPCholesky pivot rule. -/
theorem choleskyHistoryLaw_singleton [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) (h : Fin t → n) :
    (choleskyHistoryLaw A hA t).real {h} = choleskyHistoryWeight A t h := by
  classical
  rw [Measure.real, choleskyHistoryLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (choleskyHistoryWeight_nonneg hA t h)

end NLAlib

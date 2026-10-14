import NLAlib.ForMathlib.Algebra.InsertionWords
import NLAlib.Matrix.Functions.RankOneWords
import NLAlib.Matrix.Functions.CFCTrace

/-!
# Rank-one trace bounds for binary insertion words

Compressing the unmarked runs of a word gives the powers in its cyclic
rank-one trace. This connects the noncommutative binomial expansion to
the spectral estimate in `RankOneWords`.
-/

noncomputable section

namespace NLAlib

/-- The exponents before marked positions, and the final unmarked run. -/
def insertionWordGaps : List Bool → List ℕ × ℕ
  | [] => ([], 0)
  | true :: w => (0 :: (insertionWordGaps w).1, (insertionWordGaps w).2)
  | false :: w => match insertionWordGaps w with
    | ([], k) => ([], k + 1)
    | (k :: ks, t) => ((k + 1) :: ks, t)

/-- Gap compression preserves both the number of marked positions and
the total number of unmarked positions. -/
theorem insertionWordGaps_length_sum (w : List Bool) :
    (insertionWordGaps w).1.length = w.count true ∧
      (insertionWordGaps w).1.sum + (insertionWordGaps w).2 = w.count false := by
  induction w with
  | nil => simp [insertionWordGaps]
  | cons b w ih =>
    cases h : insertionWordGaps w with
    | mk ks t =>
      rw [h] at ih
      cases b <;> cases ks <;> simp_all [insertionWordGaps]
      omega

/-- The two Boolean counts add up to the length of the word. -/
theorem count_false_add_count_true_eq_length (w : List Bool) :
    w.count false + w.count true = w.length := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp_all <;> omega

section Semiring

variable {R : Type*} [Semiring R]

/-- Gap compression is an exact algebraic identity in every semiring. -/
theorem insertionWord_eq_prod_gaps_mul_pow (A X : R) (w : List Bool) :
    insertionWord A X w =
      ((insertionWordGaps w).1.map fun k => A ^ k * X).prod *
        A ^ (insertionWordGaps w).2 := by
  induction w with
  | nil => simp [insertionWordGaps, insertionWord]
  | cons b w ih =>
    cases h : insertionWordGaps w with
    | mk ks t =>
      rw [h] at ih
      cases b <;> cases ks <;>
        simp_all [insertionWordGaps, insertionWord, pow_succ', mul_assoc]

end Semiring

open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A word containing a marked factor has the same trace as a nonempty
cyclic product of powers followed by marked factors. The exponents sum
to its number of unmarked factors. -/
theorem exists_trace_insertionWord_eq_prod_pow_mul (A X : Matrix ι ι ℝ)
    (w : List Bool) (hw : 0 < w.count true) :
    ∃ ks : List ℕ, ks ≠ [] ∧ ks.length = w.count true ∧ ks.sum = w.count false ∧
      (insertionWord A X w).trace = (ks.map fun k => A ^ k * X).prod.trace := by
  obtain ⟨hl, hs⟩ := insertionWordGaps_length_sum w
  cases h : insertionWordGaps w with
  | mk ks t =>
    rw [h] at hl hs
    cases ks with
    | nil => simp only [List.length_nil] at hl; omega
    | cons k ks =>
      refine ⟨(t + k) :: ks, by simp, ?_, ?_, ?_⟩
      · simpa only [List.length_cons] using hl
      · simp only [List.sum_cons] at hs ⊢
        omega
      · rw [insertionWord_eq_prod_gaps_mul_pow, h]
        simp only [List.map_cons, List.prod_cons]
        rw [Matrix.trace_mul_comm _ (A ^ t), pow_add]
        simp only [Matrix.mul_assoc]

/-- A word with no marked positions is the ordinary power. -/
theorem insertionWord_eq_pow_of_count_true_eq_zero (A X : Matrix ι ι ℝ)
    (w : List Bool) (hw : w.count true = 0) :
    insertionWord A X w = A ^ w.count false := by
  obtain ⟨hl, hs⟩ := insertionWordGaps_length_sum w
  rw [hw] at hl
  have he := List.length_eq_zero_iff.mp hl
  rw [insertionWord_eq_prod_gaps_mul_pow, he]
  simp only [List.map_nil, List.prod_nil, Matrix.one_mul]
  rw [he] at hs
  simpa using congrArg (fun k => A ^ k) hs

/-- The absolute trace of a real symmetric power is at most its
absolute spectral trace moment. -/
theorem abs_trace_pow_le_trace_cfc_abs_pow {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (k : ℕ) :
    |(A ^ k).trace| ≤ (cfc (fun x : ℝ => |x| ^ k) A).trace := by
  rw [trace_pow_eq_sum_eigenvalues hA, trace_cfc_eq_sum_eigenvalues hA]
  simpa only [abs_pow, RCLike.ofReal_real_eq_id, id] using
    Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => hA.eigenvalues i ^ k)

/-- The trace of any insertion word with rank-one positive marked factor
is bounded by one absolute spectral moment; all insertion positions have
the same bound. -/
theorem abs_trace_insertionWord_vecMulVec_le
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : ι → ℝ)
    (w : List Bool) (hw : 0 < w.count true) :
    |(insertionWord A (vecMulVec y y) w).trace| ≤
      (y ⬝ᵥ y) ^ (w.count true - 1) *
        (y ⬝ᵥ (cfc (fun x : ℝ => |x| ^ w.count false) A *ᵥ y)) := by
  obtain ⟨ks, hne, hl, hs, ht⟩ :=
    exists_trace_insertionWord_eq_prod_pow_mul A (vecMulVec y y) w hw
  rw [ht]
  simpa only [hl, hs] using abs_trace_prod_pow_mul_vecMulVec_le hA y ks hne

/-- The canonical positive trace moment bounds every rank-one insertion
word, including the zero-insertion case. -/
theorem abs_trace_insertionWord_vecMulVec_le_trace_mul_pow
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : ι → ℝ) (w : List Bool) :
    |(insertionWord A (vecMulVec y y) w).trace| ≤
      (cfc (fun x : ℝ => |x| ^ w.count false) A *
        vecMulVec y y ^ w.count true).trace := by
  cases h : w.count true with
  | zero =>
    rw [pow_zero, Matrix.mul_one, insertionWord_eq_pow_of_count_true_eq_zero _ _ _ h]
    exact abs_trace_pow_le_trace_cfc_abs_pow hA _
  | succ p =>
    rw [trace_mul_vecMulVec_pow_succ]
    simpa only [h, Nat.add_sub_cancel] using
      abs_trace_insertionWord_vecMulVec_le hA y w (by omega)

end NLAlib

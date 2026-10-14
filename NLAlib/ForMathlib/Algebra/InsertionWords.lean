import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Noncommutative binomial words

`insertionWords n j` lists the binary words of length `n` with `j` marked
positions. Its cardinality is `n.choose j`. Evaluating these words at two
elements of a semiring gives a binomial expansion without commutativity.
-/

namespace NLAlib

/-- Binary words of length `n` with precisely `j` marked positions. -/
def insertionWords : ℕ → ℕ → List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => (insertionWords n 0).map (false :: ·)
  | n + 1, j + 1 => (insertionWords n (j + 1)).map (false :: ·) ++
      (insertionWords n j).map (true :: ·)

/-- There are `n.choose j` insertion words. -/
theorem length_insertionWords (n j : ℕ) : (insertionWords n j).length = n.choose j := by
  induction n generalizing j with
  | zero => cases j <;> simp [insertionWords]
  | succ n ih => cases j <;> simp [insertionWords, ih, Nat.choose_succ_succ, Nat.add_comm]

/-- Every insertion word has the specified length and number of marked positions. -/
theorem length_and_count_of_mem_insertionWords {n j : ℕ} {w : List Bool}
    (hw : w ∈ insertionWords n j) : w.length = n ∧ w.count true = j := by
  induction n generalizing j w with
  | zero =>
    cases j with
    | zero => simp only [insertionWords, List.mem_singleton] at hw; subst w; simp
    | succ j => simp [insertionWords] at hw
  | succ n ih =>
    cases j with
    | zero =>
      simp only [insertionWords, List.mem_map] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨hl, hc⟩ := ih hv
      simp [hl, hc]
    | succ j =>
      simp only [insertionWords, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · obtain ⟨hl, hc⟩ := ih hv
        simp [hl, hc]
      · obtain ⟨hl, hc⟩ := ih hv
        simp [hl, hc]

/-- Insertion words vanish when more positions are marked than available. -/
theorem insertionWords_eq_nil_of_lt {n j : ℕ} (hnj : n < j) :
    insertionWords n j = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_insertionWords, Nat.choose_eq_zero_of_lt hnj]

section Semiring

variable {R : Type*} [Semiring R]

/-- Evaluate a binary insertion word at an ordinary factor and a marked factor. -/
def insertionWord (A X : R) (w : List Bool) : R :=
  (w.map fun b => if b then X else A).prod

/-- The zero-insertion binomial coefficient is the corresponding power. -/
theorem sum_insertionWords_zero (A X : R) (n : ℕ) :
    ((insertionWords n 0).map (insertionWord A X)).sum = A ^ n := by
  induction n with
  | zero => simp [insertionWords, insertionWord]
  | succ n ih =>
    simp only [insertionWords, List.map_map, Function.comp_def, insertionWord,
      List.map_cons, Bool.false_eq_true, ↓reduceIte, List.prod_cons] at *
    rw [List.sum_map_mul_left]
    change A * ((insertionWords n 0).map (insertionWord A X)).sum = _
    rw [ih, pow_succ']

/-- Each noncommutative coefficient satisfies Pascal's insertion recursion. -/
theorem sum_insertionWords_succ_succ (A X : R) (n j : ℕ) :
    ((insertionWords (n + 1) (j + 1)).map (insertionWord A X)).sum =
      A * ((insertionWords n (j + 1)).map (insertionWord A X)).sum +
        X * ((insertionWords n j).map (insertionWord A X)).sum := by
  simp only [insertionWords, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, insertionWord, List.map_cons, List.prod_cons,
    Bool.false_eq_true, ↓reduceIte, List.sum_map_mul_left]
  rfl

/-- Summing all insertion coefficients gives the noncommutative binomial expansion. -/
theorem sum_sum_insertionWords_eq_add_pow (A X : R) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      ((insertionWords n j).map (insertionWord A X)).sum) = (A + X) ^ n := by
  induction n with
  | zero => simp [insertionWords, insertionWord]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp_rw [sum_insertionWords_succ_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_insertionWords_zero, ih]
    have hz : ((insertionWords n (n + 1)).map (insertionWord A X)).sum = 0 := by
      rw [insertionWords_eq_nil_of_lt (Nat.lt_succ_self n)]
      simp
    have hs : (∑ j ∈ Finset.range (n + 1),
        ((insertionWords n (j + 1)).map (insertionWord A X)).sum) + A ^ n =
          (A + X) ^ n := by
      conv_lhs => rw [Finset.sum_range_succ, hz, add_zero]
      rw [← ih, Finset.sum_range_succ' _ n, sum_insertionWords_zero]
    calc
      _ = A * ((∑ j ∈ Finset.range (n + 1),
          ((insertionWords n (j + 1)).map (insertionWord A X)).sum) + A ^ n) +
            X * (A + X) ^ n := by rw [pow_succ']; noncomm_ring
      _ = _ := by rw [hs, ← add_mul, ← pow_succ']

end Semiring

/-- Expand each marked position into either a retained mark or a deleted
identity factor. The first coordinate counts the deletions. -/
def subInsertionWords : List Bool → List (ℕ × List Bool)
  | [] => [(0, [])]
  | false :: w => (subInsertionWords w).map fun v => (v.1, false :: v.2)
  | true :: w => ((subInsertionWords w).map fun v => (v.1, true :: v.2)) ++
      ((subInsertionWords w).map fun v => (v.1 + 1, v.2))

/-- Each marked position gives two choices in the identity expansion. -/
theorem length_subInsertionWords (w : List Bool) :
    (subInsertionWords w).length = 2 ^ w.count true := by
  induction w with
  | nil => simp [subInsertionWords]
  | cons b w ih =>
    cases b with
    | false => simpa [subInsertionWords] using ih
    | true => simp [subInsertionWords, ih, pow_succ, Nat.mul_two]

/-- Deleting marked positions preserves every unmarked position and
accounts for all the original marks. -/
theorem counts_of_mem_subInsertionWords {w : List Bool} {v : ℕ × List Bool}
    (hv : v ∈ subInsertionWords w) :
    v.2.count false = w.count false ∧ v.2.count true + v.1 = w.count true := by
  induction w generalizing v with
  | nil => simp only [subInsertionWords, List.mem_singleton] at hv; subst v; simp
  | cons b w ih =>
    cases b with
    | false =>
      simp only [subInsertionWords, List.mem_map] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨hf, ht⟩ := ih hu
      simp_all
    | true =>
      simp only [subInsertionWords, List.mem_append, List.mem_map] at hv
      rcases hv with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · obtain ⟨hf, ht⟩ := ih hu
        constructor
        · simpa using hf
        · simp only [List.count_cons_self]
          omega
      · obtain ⟨hf, ht⟩ := ih hu
        constructor
        · simpa using hf
        · simp only [List.count_cons_self]
          omega

section Ring

variable {R : Type*} [Ring R]

/-- Subtracting the identity in every marked position expands into
signed words with some marked positions deleted. No factors commute. -/
theorem insertionWord_sub_one_eq_sum (A H : R) (w : List Bool) :
    insertionWord A (H - 1) w =
      ((subInsertionWords w).map fun v => (-1 : R) ^ v.1 *
        insertionWord A H v.2).sum := by
  induction w with
  | nil => simp [subInsertionWords, insertionWord]
  | cons b w ih =>
    cases b with
    | false =>
      simp only [subInsertionWords, List.map_map, Function.comp_def,
        insertionWord, List.map_cons, Bool.false_eq_true, ↓reduceIte, List.prod_cons]
      change A * insertionWord A (H - 1) w = _
      rw [ih]
      have hterm (v : ℕ × List Bool) :
          (-1 : R) ^ v.1 * (A * insertionWord A H v.2) =
            A * ((-1 : R) ^ v.1 * insertionWord A H v.2) := by
        rw [← mul_assoc, ((Commute.neg_one_left A).pow_left v.1).eq, mul_assoc]
      change A * ((subInsertionWords w).map fun v =>
          (-1 : R) ^ v.1 * insertionWord A H v.2).sum =
        ((subInsertionWords w).map fun v =>
          (-1 : R) ^ v.1 * (A * insertionWord A H v.2)).sum
      simp_rw [hterm]
      rw [List.sum_map_mul_left]
    | true =>
      simp only [subInsertionWords, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, insertionWord, List.map_cons, ↓reduceIte, List.prod_cons]
      change (H - 1) * insertionWord A (H - 1) w = _
      rw [ih]
      have hterm (v : ℕ × List Bool) :
          (-1 : R) ^ v.1 * (H * insertionWord A H v.2) =
            H * ((-1 : R) ^ v.1 * insertionWord A H v.2) := by
        rw [← mul_assoc, ((Commute.neg_one_left H).pow_left v.1).eq, mul_assoc]
      change (H - 1) * ((subInsertionWords w).map fun v =>
          (-1 : R) ^ v.1 * insertionWord A H v.2).sum =
        ((subInsertionWords w).map fun v =>
          (-1 : R) ^ v.1 * (H * insertionWord A H v.2)).sum +
        ((subInsertionWords w).map fun v =>
          (-1 : R) ^ (v.1 + 1) * insertionWord A H v.2).sum
      simp_rw [hterm, List.sum_map_mul_left, pow_succ, mul_neg_one, neg_mul]
      have hn (l : List (ℕ × List Bool)) :
          (l.map fun v => -((-1 : R) ^ v.1 * insertionWord A H v.2)).sum =
            -(l.map fun v => (-1 : R) ^ v.1 * insertionWord A H v.2).sum := by
        induction l with
        | nil => simp
        | cons v l ih => simp [ih, add_comm]
      rw [hn]
      noncomm_ring

end Ring

end NLAlib

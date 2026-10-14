import NLAlib.Matrix.Functions.InsertionWordBounds
import NLAlib.Matrix.Functions.TracePowers

/-!
# Centered rank-one insertion words

Single insertions have a cyclic linear trace, two insertions retain the
quadratic variance, and higher centered words expand into rank-one words.
These are the deterministic inputs to the finite-moment covariance bound.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A word with one insertion has the cyclic trace of that insertion
times the full ordinary power. -/
theorem trace_insertionWord_of_count_true_eq_one (A X : Matrix ι ι ℝ)
    (w : List Bool) (hw : w.count true = 1) :
    (insertionWord A X w).trace = (A ^ w.count false * X).trace := by
  obtain ⟨ks, _, hl, hs, ht⟩ := exists_trace_insertionWord_eq_prod_pow_mul A X w (by omega)
  rw [hw] at hl
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hl
  simp only [List.sum_singleton] at hs
  simpa only [List.map_singleton, List.prod_singleton, hs] using ht

/-- Complexification carries the two-insertion trace AM--GM inequality
back to real symmetric matrices. -/
theorem trace_mul_pow_mul_le_trace_sq_mul_pow
    (C A : Matrix ι ι ℝ) (hC : C.IsHermitian) (hA : A.IsHermitian)
    {n l : ℕ} (hn : Even n) (hl : l ≤ n) :
    (C * A ^ l * C * A ^ (n - l)).trace ≤ (C ^ 2 * A ^ n).trace := by
  let f : ℝ →+* ℂ := Complex.ofRealHom
  have hCm : (C.map f).IsHermitian := hC.map f (by intro x; simp [f])
  have hAm : (A.map f).IsHermitian := hA.map f (by intro x; simp [f])
  have hb := re_trace_mul_pow_mul_le_trace_sq_mul_pow (C.map f) (A.map f) hCm hAm hn hl
  have htrace (B : Matrix ι ι ℝ) : (B.map f).trace.re = B.trace := by
    simp [Matrix.trace, Matrix.diag, f]
  simp only [← Matrix.map_pow, ← Matrix.map_mul, htrace] at hb
  exact hb

/-- Two insertions in an even trace word are bounded by the quadratic
variance trace, with no absolute-moment replacement of the variance. -/
theorem trace_insertionWord_le_of_count_true_eq_two
    (A X : Matrix ι ι ℝ) (hA : A.IsHermitian) (hX : X.IsHermitian)
    (w : List Bool) (hw : w.count true = 2) (hn : Even (w.count false)) :
    (insertionWord A X w).trace ≤ (A ^ w.count false * X ^ 2).trace := by
  obtain ⟨ks, _, hl, hs, ht⟩ := exists_trace_insertionWord_eq_prod_pow_mul A X w (by omega)
  rw [hw] at hl
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
  simp only [List.sum_cons, List.sum_nil, add_zero] at hs
  rw [ht]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  have hb := trace_mul_pow_mul_le_trace_sq_mul_pow X A hX hA hn
    (show b ≤ w.count false by omega)
  rw [show w.count false - b = a by omega, Matrix.trace_mul_comm (X ^ 2)] at hb
  calc
    _ = (X * A ^ b * X * A ^ a).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
      simp only [Matrix.mul_assoc]
    _ ≤ _ := hb

private theorem trace_neg_one_pow_mul (B : Matrix ι ι ℝ) (n : ℕ) :
    (((-1 : Matrix ι ι ℝ) ^ n) * B).trace = (-1 : ℝ) ^ n * B.trace := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_neg_one, neg_mul, Matrix.trace_neg, ih,
      pow_succ, mul_neg_one, neg_mul]

/-- Expanding a centered rank-one word and taking absolute values keeps
the absolute spectral factor and every rank-one moment. -/
theorem abs_trace_insertionWord_vecMulVec_sub_one_le_sum
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : ι → ℝ) (w : List Bool) :
    |(insertionWord A (vecMulVec y y - 1) w).trace| ≤
      ((subInsertionWords w).map fun v =>
        (cfc (fun x : ℝ => |x| ^ w.count false) A *
          vecMulVec y y ^ v.2.count true).trace).sum := by
  rw [insertionWord_sub_one_eq_sum]
  have hsum : ∀ ls : List (ℕ × List Bool),
      (ls.map fun v => (-1 : Matrix ι ι ℝ) ^ v.1 *
        insertionWord A (vecMulVec y y) v.2).sum.trace =
      (ls.map fun v => (-1 : ℝ) ^ v.1 *
        (insertionWord A (vecMulVec y y) v.2).trace).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons v ls ih => simp [ih, Matrix.trace_add, trace_neg_one_pow_mul]
  rw [hsum]
  have hbound : ∀ ls : List (ℕ × List Bool), (∀ v ∈ ls, v ∈ subInsertionWords w) →
      |(ls.map fun v => (-1 : ℝ) ^ v.1 *
        (insertionWord A (vecMulVec y y) v.2).trace).sum| ≤
      (ls.map fun v => (cfc (fun x : ℝ => |x| ^ w.count false) A *
        vecMulVec y y ^ v.2.count true).trace).sum := by
    intro ls
    induction ls with
    | nil => intro _; simp
    | cons v ls ih =>
      intro hmem
      have hv := (counts_of_mem_subInsertionWords (hmem v (by simp))).1
      simp only [List.map_cons, List.sum_cons]
      apply (abs_add_le _ _).trans
      apply add_le_add _ (ih fun u hu => hmem u (List.mem_cons_of_mem _ hu))
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      simpa only [hv] using abs_trace_insertionWord_vecMulVec_le_trace_mul_pow hA y v.2
  exact hbound _ (fun _ h => h)

end NLAlib

import NLAlib.ForMathlib.Algebra.InsertionWords
import NLAlib.Matrix.Functions.InsertionWordBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Integrating the noncommutative binomial expansion

Insertion words have the usual binomial cardinalities even when their
matrix factors do not commute. A separate budget at each insertion order
therefore bounds the integral of the complete trace power.
-/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrating a list sum of trace words commutes with both finite sums. -/
theorem integrable_and_integral_sum_trace_words (A : Matrix ι ι ℝ)
    (X : Ω → Matrix ι ι ℝ) (ws : List (List Bool))
    (hi : ∀ w ∈ ws, Integrable (fun ω => (insertionWord A (X ω) w).trace) μ) :
    Integrable (fun ω => ((ws.map fun w => insertionWord A (X ω) w).sum).trace) μ ∧
      (∫ ω, ((ws.map fun w => insertionWord A (X ω) w).sum).trace ∂μ) =
        (ws.map fun w => ∫ ω, (insertionWord A (X ω) w).trace ∂μ).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hit, het⟩ := ih fun v hv => hi v (List.mem_cons_of_mem _ hv)
    have hiw := hi w (by simp)
    simp only [List.map_cons, List.sum_cons, Matrix.trace_add]
    refine ⟨hiw.add hit, ?_⟩
    rw [integral_add hiw hit, het]

/-- The integral of a matrix trace power is the sum of the integrated
insertion coefficients. -/
theorem integrable_and_integral_trace_add_pow_eq_sum_insertionWords
    (A : Matrix ι ι ℝ) (X : Ω → Matrix ι ι ℝ) (n : ℕ)
    (hi : ∀ j ≤ n, ∀ w ∈ insertionWords n j,
      Integrable (fun ω => (insertionWord A (X ω) w).trace) μ) :
    Integrable (fun ω => ((A + X ω) ^ n).trace) μ ∧
      (∫ ω, ((A + X ω) ^ n).trace ∂μ) =
        ∑ j ∈ Finset.range (n + 1),
          ((insertionWords n j).map fun w =>
            ∫ ω, (insertionWord A (X ω) w).trace ∂μ).sum := by
  have hj (j : ℕ) (hj : j ≤ n) :=
    integrable_and_integral_sum_trace_words A X (insertionWords n j) (hi j hj)
  have he (ω : Ω) : ((A + X ω) ^ n).trace =
      ∑ j ∈ Finset.range (n + 1),
        (((insertionWords n j).map (insertionWord A (X ω))).sum).trace := by
    rw [← sum_sum_insertionWords_eq_add_pow A (X ω) n, Matrix.trace_sum]
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun j hj' => (hj j (by simpa using Finset.mem_range.mp hj')).1)
  · simp_rw [he]
    rw [integral_finsetSum _ (fun j hj' => (hj j (by simpa using Finset.mem_range.mp hj')).1)]
    apply Finset.sum_congr rfl
    intro j hj'
    exact (hj j (by simpa using Finset.mem_range.mp hj')).2

/-- Uniform per-word budgets sum to binomial coefficient budgets. -/
theorem integral_trace_add_pow_le_sum_choose
    (A : Matrix ι ι ℝ) (X : Ω → Matrix ι ι ℝ) (n : ℕ) (b : ℕ → ℝ)
    (hi : ∀ j ≤ n, ∀ w ∈ insertionWords n j,
      Integrable (fun ω => (insertionWord A (X ω) w).trace) μ)
    (hb : ∀ j ≤ n, ∀ w ∈ insertionWords n j,
      (∫ ω, (insertionWord A (X ω) w).trace ∂μ) ≤ b j) :
    (∫ ω, ((A + X ω) ^ n).trace ∂μ) ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * b j := by
  rw [(integrable_and_integral_trace_add_pow_eq_sum_insertionWords A X n hi).2]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hs : ∀ ws : List (List Bool), (∀ w ∈ ws, w ∈ insertionWords n j) →
      (ws.map fun w => ∫ ω, (insertionWord A (X ω) w).trace ∂μ).sum ≤
        (ws.length : ℝ) * b j := by
    intro ws
    induction ws with
    | nil => intro _; simp
    | cons w ws ih =>
      intro hmem
      have hbt := ih (fun v hv => hmem v (List.mem_cons_of_mem _ hv))
      have hbw := hb j hjn w (hmem w (by simp))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
  simpa only [length_insertionWords] using hs _ (fun _ h => h)

/-- Removing the centered linear term leaves the factorial coefficient
recurrence used by the covariance moment comparison. -/
theorem integral_trace_add_pow_le_of_centered_word_budgets
    (A : Matrix ι ι ℝ) (X : Ω → Matrix ι ι ℝ) {n : ℕ} (hn : 2 ≤ n)
    (ν R : ℝ) (T : ℕ → ℝ)
    (hi : ∀ j ≤ n, ∀ w ∈ insertionWords n j,
      Integrable (fun ω => (insertionWord A (X ω) w).trace) μ)
    (hlinear : ∀ w ∈ insertionWords n 1,
      (∫ ω, (insertionWord A (X ω) w).trace ∂μ) = 0)
    (hbudget : ∀ j, 2 ≤ j → j ≤ n → ∀ w ∈ insertionWords n j,
      (∫ ω, (insertionWord A (X ω) w).trace ∂μ) ≤
        (j.factorial : ℝ) / 2 * ν * R ^ (j - 2) * T (n - j)) :
    (∫ ω, ((A + X ω) ^ n).trace ∂μ) ≤ (A ^ n).trace +
      ∑ k ∈ Finset.range (n - 1),
        (n.choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 *
          ν * R ^ k * T (n - (k + 2)) := by
  let b (j : ℕ) : ℝ := if j = 0 then (A ^ n).trace else
    if j = 1 then 0 else (j.factorial : ℝ) / 2 * ν * R ^ (j - 2) * T (n - j)
  have hb : ∀ j ≤ n, ∀ w ∈ insertionWords n j,
      (∫ ω, (insertionWord A (X ω) w).trace ∂μ) ≤ b j := by
    intro j hj w hw
    by_cases hj0 : j = 0
    · subst j
      have hword : (fun ω => insertionWord A (X ω) w) = fun _ => A ^ n := by
        obtain ⟨hl, hc⟩ := length_and_count_of_mem_insertionWords hw
        have hf := count_false_add_count_true_eq_length w
        have hn' : w.count false = n := by omega
        funext ω
        rw [insertionWord_eq_pow_of_count_true_eq_zero _ _ w hc, hn']
      have hword' (ω : Ω) : insertionWord A (X ω) w = A ^ n := congrFun hword ω
      simp only [hword']
      simp [b]
    · by_cases hj1 : j = 1
      · subst j
        simp only [b, if_neg (by decide : (1 : ℕ) ≠ 0)]
        exact (hlinear w hw).le
      · simpa only [b, if_neg hj0, if_neg hj1] using hbudget j (by omega) hj w hw
  have h := integral_trace_add_pow_le_sum_choose A X n b hi hb
  have hbase : (∑ j ∈ Finset.range 2, (n.choose j : ℝ) * b j) = (A ^ n).trace := by
    simp [Finset.sum_range_succ, b]
  have htail : (∑ k ∈ Finset.range (n - 1), (n.choose (2 + k) : ℝ) * b (2 + k)) =
      ∑ k ∈ Finset.range (n - 1),
        (n.choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 *
          ν * R ^ k * T (n - (k + 2)) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [b]
    rw [if_neg (by omega : 2 + k ≠ 0), if_neg (by omega : 2 + k ≠ 1)]
    rw [show 2 + k - 2 = k by omega, Nat.add_comm 2 k]
    ring
  rw [show n + 1 = 2 + (n - 1) by omega, Finset.sum_range_add, hbase, htail] at h
  exact h

end NLAlib

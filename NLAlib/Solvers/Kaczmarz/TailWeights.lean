/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
# Finite geometric weights for tail-averaged Kaczmarz

The coefficient of initial error in a length-`N` tail is
`∑ t < N, (2t+1)q^t`. The bounds below retain `q=0`, never divide by `q`,
and yield both constants in the tail-averaging theorem.
Source: Epperly–Goldshlager–Webber, arXiv:2411.19877v3, Theorems 2–3.
-/

namespace NLAlib.Kaczmarz

/-- Initial-error weight in the unnormalized sum of `N` correlated iterates. -/
noncomputable def tailInitialWeight (q : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, (2 * (t : ℝ) + 1) * q ^ t

@[simp] theorem tailInitialWeight_zero (q : ℝ) : tailInitialWeight q 0 = 0 := by
  simp [tailInitialWeight]

/-- Nonnegativity of the finite initial-error weight. -/
theorem tailInitialWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (N : ℕ) :
    0 ≤ tailInitialWeight q N := by
  unfold tailInitialWeight
  exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity) (pow_nonneg hq t)

/-- First-step decomposition of the finite initial-error weight. -/
theorem tailInitialWeight_succ (q : ℝ) (N : ℕ) :
    tailInitialWeight q (N + 1) =
      1 + 2 * (∑ t ∈ Finset.range N, q ^ (t + 1)) + q * tailInitialWeight q N := by
  unfold tailInitialWeight
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, mul_one]
  rw [Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- The diagonal plus twice the finite positive-lag sum is at most `(1+q)/(1-q)`. -/
theorem one_add_two_mul_sum_pow_succ_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    1 + 2 * (∑ t ∈ Finset.range N, q ^ (t + 1)) ≤ (1 + q) / (1 - q) := by
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0 hq1
  rw [← Finset.range_eq_Ico, pow_zero] at hg
  have hs : (∑ t ∈ Finset.range N, q ^ (t + 1)) = q * ∑ t ∈ Finset.range N, q ^ t := by
    simp_rw [pow_succ', Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ 1 + 2 * (q * (1 / (1 - q))) := by gcongr
    _ = _ := by field_simp [ne_of_gt (sub_pos.mpr hq1)]; ring

/-- The initial-error weight never exceeds the square of the averaging length. -/
theorem tailInitialWeight_le_sq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    tailInitialWeight q N ≤ (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp : q ^ N ≤ 1 := pow_le_one₀ hq0 hq1
    rw [tailInitialWeight, Finset.sum_range_succ]
    change tailInitialWeight q N + (2 * (N : ℝ) + 1) * q ^ N ≤ _
    have ht := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * (N : ℝ) + 1 by positivity)
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The initial-error weight is at most the averaging length times the geometric
correlation factor. -/
theorem tailInitialWeight_le_mul {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    tailInitialWeight q N ≤ ((1 + q) / (1 - q)) * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [tailInitialWeight_succ]
    have hc := one_add_two_mul_sum_pow_succ_le hq0 hq1 N
    have hq := mul_le_mul_of_nonneg_right hq1.le (tailInitialWeight_nonneg hq0 N)
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The uniform initial-error coefficient is `(1+q)/(1-q)^2`. -/
theorem tailInitialWeight_le_div {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    tailInitialWeight q N ≤ ((1 + q) / (1 - q)) / (1 - q) := by
  induction N with
  | zero => simp; positivity
  | succ N ih =>
    rw [tailInitialWeight_succ]
    calc
      _ ≤ (1 + q) / (1 - q) + q * (((1 + q) / (1 - q)) / (1 - q)) :=
        add_le_add (one_add_two_mul_sum_pow_succ_le hq0 hq1 N)
          (mul_le_mul_of_nonneg_left ih hq0)
      _ = _ := by field_simp [ne_of_gt (sub_pos.mpr hq1)]; ring

end NLAlib.Kaczmarz

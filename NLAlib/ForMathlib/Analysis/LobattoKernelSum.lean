import NLAlib.ForMathlib.Analysis.LobattoKernel
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Periodic

/-!
# The finite translated Lobatto kernel sum

Finite reindexing and periodicity reduce the sum of absolute cardinals to one grid cell.
Source: focused polynomial-approximation rederivations, equation `eq:cotpair`.
-/

noncomputable section

open Real Finset Set

namespace NLAlib

/-- Sum of absolute translated cardinals on the full `2n` angular grid.
Source: focused rederivations, Theorem `thm:lobatto`. -/
def lobattoKernelSum (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ range (2 * n), |lobattoKernel n (t - j * π / n)|

/-- The translated kernel sum can be paired on the two sides of the evaluation point.
Source: finite reflection of the `2n`-angle grid. -/
theorem lobattoKernelSum_eq_paired {n : ℕ} (hn : 0 < n) (t : ℝ) :
    lobattoKernelSum n t =
      (∑ j ∈ range n, |lobattoKernel n (t + j * π / n)|) +
      ∑ j ∈ range n, |lobattoKernel n (t - (j + 1 : ℕ) * π / n)| := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  let c : ℝ := π / n
  have hperiod : ∀ x : ℝ, lobattoKernel n (x + (2 * n : ℕ) * c) = lobattoKernel n x := by
    intro x
    rw [show ((2 * n : ℕ) : ℝ) * c = 2 * π by dsimp [c]; push_cast; field_simp]
    exact lobattoKernel_periodic n x
  have hsecond : (∑ j ∈ range n, |lobattoKernel n (t - (n + j : ℕ) * c)|) =
      ∑ j ∈ range n, |lobattoKernel n (t + (j + 1 : ℕ) * c)| := by
    rw [← sum_range_reflect (fun j : ℕ => |lobattoKernel n (t - (n + j : ℕ) * c)|) n]
    apply sum_congr rfl
    intro j hj
    have hj' : j ≤ n - 1 := by have := mem_range.mp hj; omega
    have heq : t + (j + 1 : ℕ) * c =
        (t - (n + (n - 1 - j) : ℕ) * c) + (2 * n : ℕ) * c := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      rw [Nat.cast_sub hj', Nat.cast_sub hn]
      norm_num
      ring
    rw [heq, hperiod]
  have hmiddle : lobattoKernel n (t + (n : ℝ) * c) = lobattoKernel n (t - (n : ℝ) * c) := by
    have hx : t - (n : ℝ) * c + (2 * n : ℕ) * c = t + (n : ℝ) * c := by push_cast; ring
    simpa only [hx] using hperiod (t - (n : ℝ) * c)
  dsimp [lobattoKernelSum]
  simp_rw [mul_div_assoc]
  change (∑ j ∈ range (2 * n), |lobattoKernel n (t - (j : ℝ) * c)|) =
    (∑ j ∈ range n, |lobattoKernel n (t + (j : ℝ) * c)|) +
      ∑ j ∈ range n, |lobattoKernel n (t - (j + 1 : ℕ) * c)|
  rw [show 2 * n = n + n by omega, sum_range_add, hsecond]
  have hm0 : (∑ j ∈ range n, |lobattoKernel n (t - (j : ℝ) * c)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t - (j + 1 : ℕ) * c)|) + |lobattoKernel n t| := by
    simpa only [Nat.sub_add_cancel hn, Nat.cast_zero, zero_mul, sub_zero] using
      sum_range_succ' (fun j : ℕ => |lobattoKernel n (t - (j : ℝ) * c)|) (n - 1)
  have hp0 : (∑ j ∈ range n, |lobattoKernel n (t + (j : ℝ) * c)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t + (j + 1 : ℕ) * c)|) + |lobattoKernel n t| := by
    simpa only [Nat.sub_add_cancel hn, Nat.cast_zero, zero_mul, add_zero] using
      sum_range_succ' (fun j : ℕ => |lobattoKernel n (t + (j : ℝ) * c)|) (n - 1)
  have hp1 : (∑ j ∈ range n, |lobattoKernel n (t + (j + 1 : ℕ) * c)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t + (j + 1 : ℕ) * c)|) + |lobattoKernel n (t + (n : ℝ) * c)| := by
    simpa only [Nat.sub_add_cancel hn] using
      sum_range_succ (fun j : ℕ => |lobattoKernel n (t + (j + 1 : ℕ) * c)|) (n - 1)
  have hm1 : (∑ j ∈ range n, |lobattoKernel n (t - (j + 1 : ℕ) * c)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t - (j + 1 : ℕ) * c)|) + |lobattoKernel n (t - (n : ℝ) * c)| := by
    simpa only [Nat.sub_add_cancel hn] using
      sum_range_succ (fun j : ℕ => |lobattoKernel n (t - (j + 1 : ℕ) * c)|) (n - 1)
  rw [hm0, hp0, hp1, hm1, hmiddle]
  ring

/-- Translation by one grid step permutes the absolute-cardinal sum.
Source: finite cyclic reindexing. -/
theorem lobattoKernelSum_periodic {n : ℕ} (hn : 0 < n) :
    Function.Periodic (lobattoKernelSum n) (π / n) := by
  intro t
  have hN : 0 < 2 * n := by omega
  have hNadd : 2 * n = (2 * n - 1) + 1 := (Nat.sub_add_cancel hN).symm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  let c : ℝ := π / n
  have hfirst : lobattoKernel n (t + c) =
      lobattoKernel n (t - ((2 * n - 1 : ℕ) : ℝ) * c) := by
    have h := lobattoKernel_periodic n (t - ((2 * n - 1 : ℕ) : ℝ) * c)
    convert h using 1
    congr 1
    dsimp [c]
    rw [Nat.cast_sub hN]
    push_cast
    field_simp
    ring
  dsimp [lobattoKernelSum]
  simp_rw [mul_div_assoc]
  change (∑ j ∈ range (2 * n), |lobattoKernel n (t + c - (j : ℝ) * c)|) =
    ∑ j ∈ range (2 * n), |lobattoKernel n (t - (j : ℝ) * c)|
  rw [hNadd, sum_range_succ', sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero, hfirst]
  have hsum : (∑ j ∈ range (2 * n - 1), |lobattoKernel n (t + c - ((j : ℝ) + 1) * c)|) =
      ∑ j ∈ range (2 * n - 1), |lobattoKernel n (t - (j : ℝ) * c)| := by
    apply sum_congr rfl
    intro j hj
    congr 2
    ring
  rw [hsum]

/-- At grid points, the translated kernel sum is one.
Source: exact finite cardinality. -/
@[simp] theorem lobattoKernelSum_zero {n : ℕ} (hn : 0 < n) : lobattoKernelSum n 0 = 1 := by
  dsimp [lobattoKernelSum]
  rw [Finset.sum_eq_single 0]
  · simp [lobattoKernel_zero hn]
  · intro j hj hj0
    simp only [zero_sub, lobattoKernel_neg]
    rw [lobattoKernel_grid_zero hn (by omega) (mem_range.mp hj), abs_zero]
  · intro h
    exact False.elim (h (by simp; omega))

/-- In an open grid cell, the positive-angle kernel has the cotangent magnitude.
Source: its closed form and sine antiperiodicity. -/
theorem abs_lobattoKernel_phase_add {n j : ℕ} (hn : 0 < n) (hj : j < n)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    |lobattoKernel n (α * π / n + j * π / n)| =
      sin (π * α) / (2 * n) * Real.cot (((j : ℝ) + α) * π / (2 * n)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hα0 : 0 < α := hα.1
  have hα1 : α < 1 := hα.2
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have ht : 0 < ((j : ℝ) + α) * π / (2 * n) := by positivity
  have htπ : ((j : ℝ) + α) * π / (2 * n) < π / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    nlinarith [pi_pos, hα1]
  have hs : 0 < sin (((j : ℝ) + α) * π / (2 * n)) :=
    sin_pos_of_pos_of_lt_pi ht (by linarith [pi_pos])
  have hc : 0 ≤ Real.cot (((j : ℝ) + α) * π / (2 * n)) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], htπ.le⟩) hs.le
  have hsin : 0 < sin (π * α) := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos, hα.2])
  have heq : (α * π / n + j * π / n) / 2 = ((j : ℝ) + α) * π / (2 * n) := by ring
  rw [lobattoKernel_eq_sin_cot hn (by rw [heq]; exact hs.ne'), heq]
  have harg : (n : ℝ) * (α * π / n + j * π / n) = π * α + j * π := by field_simp
  rw [harg, sin_add_nat_mul_pi, abs_div, abs_mul, abs_mul, abs_neg_one_pow,
    one_mul, abs_of_pos hsin, abs_of_nonneg hc, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
  ring

/-- In an open grid cell the translated absolute-cardinal sum is the paired cotangent sum.
Source: focused rederivations, equation `eq:cotpair`. -/
theorem lobattoKernelSum_phase {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    lobattoKernelSum n (α * π / n) = sin (π * α) / (2 * n) *
      ∑ j ∈ range n, (Real.cot (((j : ℝ) + α) * π / (2 * n)) +
        Real.cot (((j : ℝ) + 1 - α) * π / (2 * n))) := by
  rw [lobattoKernelSum_eq_paired hn]
  have hneg : ∀ j ∈ range n,
      |lobattoKernel n (α * π / n - (j + 1 : ℕ) * π / n)| =
      sin (π * α) / (2 * n) * Real.cot (((j : ℝ) + 1 - α) * π / (2 * n)) := by
    intro j hj
    rw [show α * π / n - (j + 1 : ℕ) * π / n = -((1 - α) * π / n + j * π / n) by push_cast; ring,
      lobattoKernel_neg, abs_lobattoKernel_phase_add hn (mem_range.mp hj) (by constructor <;> linarith [hα.1, hα.2])]
    rw [show π * (1 - α) = π - π * α by ring, sin_pi_sub]
    congr 2
    ring
  rw [sum_congr rfl (fun j hj => abs_lobattoKernel_phase_add hn (mem_range.mp hj) hα),
    sum_congr rfl hneg, ← mul_sum, ← mul_sum, ← mul_add, ← sum_add_distrib]

end NLAlib

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-! # Finite telescoping of adjacent cell boundaries

Consecutive equal shared edges cancel in finite sums. The two-dimensional
identity is independent of geometry and supports primitive-chart homotopy
arguments on finite grids.

Ported from the local deferred Jordan-contour development of 2026-10-14.
-/

namespace Finset

/-- Adjacent end and start increments telescope even when the successive
values were originally given by different functions. -/
theorem sum_range_sub_of_adjacent {G : Type*} [AddCommGroup G]
    (f g : ℕ → G) {n : ℕ} (hn : 0 < n)
    (h : ∀ i, i + 1 < n → f (i + 1) = g i) :
    ∑ i ∈ range n, (f i - g i) = f 0 - g (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [sum_sub_distrib, sum_range_succ' f, sum_range_succ g]
  have hs : (∑ i ∈ range k, f (i + 1)) = ∑ i ∈ range k, g i := by
    apply sum_congr rfl
    intro i hi
    exact h i (Nat.succ_lt_succ (mem_range.mp hi))
  rw [hs]
  simp only [Nat.succ_sub_one]
  abel

/-- Summing zero cell boundaries and cancelling actual shared edges leaves
exactly the outer boundary of a finite square grid. -/
theorem sum_grid_boundary_eq {G : Type*} [AddCommGroup G]
    (bottom top left right : ℕ → ℕ → G) {n : ℕ} (hn : 0 < n)
    (hc : ∀ i < n, ∀ j < n, bottom i j + right i j = top i j + left i j)
    (hh : ∀ i < n, ∀ j, j + 1 < n → bottom i (j + 1) = top i j)
    (hv : ∀ i, i + 1 < n → ∀ j < n, left (i + 1) j = right i j) :
    (∑ j ∈ range n, right (n - 1) j) - (∑ j ∈ range n, left 0 j) =
      (∑ i ∈ range n, top i (n - 1)) - (∑ i ∈ range n, bottom i 0) := by
  have hzero : (∑ i ∈ range n, ∑ j ∈ range n,
      ((bottom i j - top i j) + (right i j - left i j))) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    have h := hc i (mem_range.mp hi) j (mem_range.mp hj)
    calc
      _ = (bottom i j + right i j) - (top i j + left i j) := by abel
      _ = 0 := sub_eq_zero.mpr h
  simp_rw [sum_add_distrib] at hzero
  have hhorizontal : (∑ i ∈ range n, ∑ j ∈ range n, (bottom i j - top i j)) =
      ∑ i ∈ range n, (bottom i 0 - top i (n - 1)) := by
    apply sum_congr rfl
    intro i hi
    exact sum_range_sub_of_adjacent _ _ hn (hh i (mem_range.mp hi))
  have hvertical : (∑ i ∈ range n, ∑ j ∈ range n, (right i j - left i j)) =
      ∑ j ∈ range n, (right (n - 1) j - left 0 j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    have h := sum_range_sub_of_adjacent (fun i => left i j) (fun i => right i j)
      hn (fun i hi => hv i hi j (mem_range.mp hj))
    have hneg := congrArg Neg.neg h
    simpa only [← sum_neg_distrib, neg_sub] using hneg
  rw [hhorizontal, hvertical] at hzero
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  have h := eq_neg_of_add_eq_zero_right hzero
  simpa only [← sum_neg_distrib, neg_sub] using h

end Finset

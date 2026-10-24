import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Tail averaging for decreasing finite sequences

The average of the last `k` terms of a decreasing block is bounded by the
average of the whole block. Multiplication by the block length keeps the
zero-length cases and avoids division by an individual term.
-/

open scoped BigOperators

namespace Antitone

/-- The last `k` terms of the length-`l` block beginning at `k` have no
larger average than the whole block, stated without division. -/
theorem mul_sum_tail_le_mul_sum_block {a : ℕ → ℝ} (ha : Antitone a)
    {k l : ℕ} (hkl : k ≤ l) :
    (l : ℝ) * (∑ j ∈ Finset.range k, a (l + j)) ≤
      (k : ℝ) * (∑ i ∈ Finset.range l, a (k + i)) := by
  have hp : ((l - k : ℕ) : ℝ) * (∑ j ∈ Finset.range k, a (l + j)) ≤
      (k : ℝ) * (∑ i ∈ Finset.range (l - k), a (k + i)) := by
    calc
      _ = ∑ i ∈ Finset.range (l - k), ∑ j ∈ Finset.range k, a (l + j) := by simp
      _ ≤ ∑ i ∈ Finset.range (l - k), ∑ j ∈ Finset.range k, a (k + i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j _
        apply ha
        have := Finset.mem_range.mp hi
        omega
      _ = _ := by simp [Finset.mul_sum, mul_comm]
  have hs : (∑ i ∈ Finset.range l, a (k + i)) =
      (∑ i ∈ Finset.range (l - k), a (k + i)) +
        ∑ j ∈ Finset.range k, a (l + j) := by
    conv_lhs => rw [show l = (l - k) + k by omega]
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  rw [hs]
  have hc : ((l - k : ℕ) : ℝ) = (l : ℝ) - k := Nat.cast_sub hkl
  rw [hc] at hp
  nlinarith

end Antitone

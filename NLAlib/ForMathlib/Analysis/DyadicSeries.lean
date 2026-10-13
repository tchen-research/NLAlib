import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Absolute summability from geometric dyadic block bounds

A scalar sequence with nonnegative entries is summable when its dyadic block sums
are bounded by a geometric sequence. This is useful with polynomial approximation
and finite Bessel inequalities.
-/

noncomputable section

open Finset

namespace NLAlib

/-- Geometric bounds on nonnegative dyadic blocks imply summability of the entire sequence.
Source: elementary dyadic summation; used for `chebyshev-series-convergence`. -/
theorem summable_of_dyadic_block_sum_le_geometric {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    {C q : ℝ} (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hblock : ∀ j, ∑ k ∈ Ico (2 ^ j) (2 ^ (j + 1)), a k ≤ C * q ^ j) :
    Summable a := by
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq0])
  have hfinite : ∀ J, ∑ k ∈ range (2 ^ J), a k ≤ a 0 + C * ∑ j ∈ range J, q ^ j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← sum_range_add_sum_Ico a (show 2 ^ J ≤ 2 ^ (J + 1) by
        rw [pow_succ]; omega), sum_range_succ]
      have h := add_le_add ih (hblock J)
      calc _ ≤ (a 0 + C * ∑ j ∈ range J, q ^ j) + C * q ^ J := h
        _ = a 0 + C * ((∑ j ∈ range J, q ^ j) + q ^ J) := by ring
  apply summable_of_sum_range_le ha (c := a 0 + C * ∑' j : ℕ, q ^ j)
  intro m
  have hm := sum_le_sum_of_subset_of_nonneg
    (range_mono (show m ≤ 2 ^ m from (show m < 2 ^ m from Nat.lt_two_pow_self).le))
    (fun k hk hnot => ha k)
  exact hm.trans ((hfinite m).trans (add_le_add (le_refl (a 0))
    (mul_le_mul_of_nonneg_left (hgeom.sum_le_tsum (range m) (fun j hj => pow_nonneg hq0 j)) hC)))

end NLAlib

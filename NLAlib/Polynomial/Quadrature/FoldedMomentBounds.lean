import NLAlib.Polynomial.Quadrature.ChebyshevError
import Mathlib.Algebra.BigOperators.Intervals

/-! # Finite folded-moment blocks

The even Lebesgue moments telescope, and a full period of folded even moments
has total absolute mass at most four.
-/
noncomputable section
open Finset
namespace NLAlib

/-- Positive even Chebyshev moments have a telescoping reciprocal form in modulus.
Source: Trefethen, ATAP, Theorem 19.2 and focused quadrature block proof. -/
theorem abs_chebyshevMoment_two_mul_succ (j : ℕ) :
    |chebyshevMoment (2 * (j + 1))| = 1 / (2 * (j : ℝ) + 1) - 1 / (2 * j + 3) := by
  unfold chebyshevMoment
  rw [if_pos (by simp : Even (2 * (j + 1))), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  rw [abs_of_neg (by nlinarith : 1 - (2 * ((j : ℝ) + 1)) ^ 2 < 0)]
  have h0 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  rw [show -(1 - (2 * ((j : ℝ) + 1)) ^ 2) = (2 * j + 1) * (2 * j + 3) by ring]
  field_simp [h0, h1]
  ring

/-- The finite absolute positive-even moment sum is exactly `1−1/(2m+1)`.
Source: focused quadrature reroute, finite telescoping moment proof. -/
theorem sum_abs_chebyshevMoment_two_mul_succ (m : ℕ) :
    (∑ j ∈ range m, |chebyshevMoment (2 * (j + 1))|) = 1 - 1 / (2 * (m : ℝ) + 1) := by
  simp_rw [abs_chebyshevMoment_two_mul_succ]
  have h : (∑ j ∈ range m,
      (1 / (2 * (j : ℝ) + 1) - 1 / (2 * ((j + 1 : ℕ) : ℝ) + 1))) =
      1 - 1 / (2 * (m : ℝ) + 1) := by
    simpa using sum_range_sub' (fun j => 1 / (2 * (j : ℝ) + 1)) m
  convert h using 1
  apply sum_congr rfl
  intro j hj
  push_cast
  ring

/-- A full period of even folded Chebyshev moments has absolute mass at most four.
Source: focused quadrature reroute, finite block lemma.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem sum_abs_chebyshevMoment_alias_two_mul_le_four {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ range n, |chebyshevMoment (chebyshevAliasIndex n (2 * j))|) ≤ 4 := by
  let f := fun j => |chebyshevMoment (chebyshevAliasIndex n (2 * j))|
  have hf0 : f 0 = 2 := by simp [f, chebyshevAliasIndex, chebyshevMoment]
  have hsplit : (∑ j ∈ range n, f j) = 2 + ∑ j ∈ Ico 1 n, f j := by
    rw [sum_Ico_eq_sub f hn, show (∑ j ∈ range 1, f j) = 2 by simpa using hf0]
    ring
  have hterm (j : ℕ) (hj : j ∈ Ico 1 n) :
      f j ≤ |chebyshevMoment (2 * j)| + |chebyshevMoment (2 * (n - j))| := by
    have hjn : j < n := (mem_Ico.mp hj).2
    have halias : chebyshevAliasIndex n (2 * j) = min (2 * j) (2 * (n - j)) := by
      unfold chebyshevAliasIndex
      rw [Nat.mod_eq_of_lt (by omega), Nat.mul_sub_left_distrib]
    dsimp [f]
    rw [halias]
    rcases le_or_gt (2 * j) (2 * (n - j)) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [min_eq_right h.le]
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hrefl : (∑ j ∈ Ico 1 n, |chebyshevMoment (2 * (n - j))|) =
      ∑ j ∈ Ico 1 n, |chebyshevMoment (2 * j)| := by
    simpa using sum_Ico_reflect (fun j => |chebyshevMoment (2 * j)|) 1 (m := n) (n := n) (by omega)
  have hsum : (∑ j ∈ Ico 1 n, |chebyshevMoment (2 * j)|) ≤ 1 := by
    rw [sum_Ico_eq_sum_range]
    have heq : (∑ j ∈ range (n - 1), |chebyshevMoment (2 * (1 + j))|) =
        ∑ j ∈ range (n - 1), |chebyshevMoment (2 * (j + 1))| := by
      apply sum_congr rfl
      intro j hj
      rw [Nat.add_comm 1 j]
    rw [heq, sum_abs_chebyshevMoment_two_mul_succ]
    exact sub_le_self _ (by positivity)
  change (∑ j ∈ range n, f j) ≤ 4
  rw [hsplit]
  have hbound := sum_le_sum hterm
  rw [sum_add_distrib, hrefl] at hbound
  linarith

end NLAlib

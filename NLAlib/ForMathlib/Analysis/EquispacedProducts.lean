import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Products for equally spaced interpolation nodes

Factorial denominators and a half-grid-point product bound give the explicit
exponential lower bound for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Finset
open scoped Nat

namespace NLAlib

/-- The absolute cardinal denominator on the integer grid is a pair of factorials.
Source: the equispaced reroute, finite cardinal product formula. -/
theorem prod_abs_natCast_sub_eq_factorial {n j : ℕ} (hj : j ≤ n) :
    (∏ k ∈ (range (n + 1)).erase j, |(j : ℝ) - k|) = (j ! : ℝ) * ((n - j)! : ℝ) := by
  induction n with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      norm_num
  | succ n ih =>
      by_cases hjn : j = n + 1
      · subst j
        rw [range_add_one, erase_insert (by simp)]
        have hprod : (∏ k ∈ range (n + 1), |((n + 1 : ℕ) : ℝ) - k|) = ((n + 1)! : ℝ) := by
          calc
            _ = ∏ k ∈ range (n + 1), (((n + 1 : ℕ) : ℝ) - k) := by
              apply prod_congr rfl
              intro k hk
              exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (mem_range.mp hk).le))
            _ = ((n + 1).descFactorial (n + 1) : ℝ) := by
              rw [prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range]
            _ = _ := by rw [Nat.descFactorial_self]
        simpa using hprod
      · have hjn' : j ≤ n := by omega
        rw [range_add_one, erase_insert_of_ne (by omega), prod_insert (by simp), ih hjn']
        have hcast : |(j : ℝ) - ((n + 1 : ℕ) : ℝ)| = ((n + 1 - j : ℕ) : ℝ) := by
          rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hj)), Nat.cast_sub hj]
          ring
        rw [hcast, show n + 1 - j = (n - j) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
        ring

/-- The normalized nodal product at the first half-grid point is at least `1/(4n)`.
Source: equispaced reroute, the product comparison with `(k−1)/k`. -/
theorem one_div_four_mul_nat_le_abs_half_grid_product {n : ℕ} (hn : 0 < n) :
    1 / (4 * (n : ℝ)) ≤ |∏ k ∈ range (n + 1), ((1 : ℝ) / 2 - k)| / (n ! : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num [prod_range_succ]
      · have hnpos : 0 < n := by omega
        have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
        have hfact : 0 < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
        have hrec : |∏ k ∈ range (n + 1 + 1), ((1 : ℝ) / 2 - k)| / ((n + 1)! : ℝ) =
            (|∏ k ∈ range (n + 1), ((1 : ℝ) / 2 - k)| / (n ! : ℝ)) *
              (((n : ℝ) + 1 / 2) / (n + 1)) := by
          have habs : |(1 : ℝ) / 2 - ((n + 1 : ℕ) : ℝ)| = (n : ℝ) + 1 / 2 := by
            rw [abs_of_nonpos (by push_cast; linarith)]
            push_cast
            ring
          rw [prod_range_succ, abs_mul, Nat.factorial_succ, Nat.cast_mul, habs]
          push_cast
          field_simp
        rw [hrec]
        calc
          _ ≤ (1 / (4 * (n : ℝ))) * (((n : ℝ) + 1 / 2) / (n + 1)) := by
            push_cast
            calc
              _ = (1 / (4 * (n : ℝ))) * ((n : ℝ) / (n + 1)) := by
                field_simp
              _ ≤ _ := by gcongr; linarith
          _ ≤ _ := mul_le_mul_of_nonneg_right (ih hnpos) (by positivity)

end NLAlib

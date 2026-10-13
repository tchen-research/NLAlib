import NLAlib.ForMathlib.Analysis.EquispacedProducts
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Lagrange cardinal values on the integer grid

The half-grid value has an exact factorial/binomial expression. Helper for the
equispaced half of `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Polynomial Finset
open scoped Nat

namespace NLAlib

/-- The magnitude of each cardinal at the first half-grid point is an exact binomial term.
Source: operator reroutes, the equispaced finite cardinal formula. -/
theorem abs_eval_lagrange_basis_nat_half {n j : ℕ} (hj : j ≤ n) :
    |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)| =
      (|∏ k ∈ range (n + 1), ((1 : ℝ) / 2 - k)| / (n ! : ℝ)) *
        (n.choose j : ℝ) / |(j : ℝ) - 1 / 2| := by
  have hhalf : (1 : ℝ) / 2 ≠ (j : ℝ) := by
    by_cases hj0 : j = 0
    · subst j; norm_num
    · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      linarith
  have hw : |Lagrange.nodalWeight (range (n + 1)) (fun k : ℕ => (k : ℝ)) j| =
      ((j ! : ℝ) * ((n - j)! : ℝ))⁻¹ := by
    rw [Lagrange.nodalWeight, prod_inv_distrib, abs_inv, abs_prod,
      prod_abs_natCast_sub_eq_factorial hj]
  rw [Lagrange.eval_basis_not_at_node (mem_range.mpr (by omega)) hhalf, abs_mul, abs_mul,
    hw, abs_inv, abs_sub_comm]
  simp only [Lagrange.eval_nodal]
  have hf0 : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hj0 : (j ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnj0 : ((n - j)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - j)
  have hchoose : (n.choose j : ℝ) * (j ! : ℝ) * ((n - j)! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hratio : ((j ! : ℝ) * ((n - j)! : ℝ))⁻¹ = (n ! : ℝ)⁻¹ * (n.choose j : ℝ) := by
    field_simp
    nlinarith [hchoose]
  rw [hratio]
  ring

/-- The sum of cardinal magnitudes on the integer grid has the strict exponential bound.
Source: operator reroutes, the binomial sum and half-grid product comparison. -/
theorem pow_two_div_four_mul_sq_lt_sum_abs_lagrange_basis {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) ^ n / (4 * (n : ℝ) ^ 2) <
      ∑ j ∈ range (n + 1),
        |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)| := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod := one_div_four_mul_nat_le_abs_half_grid_product hn
  have hprodpos : 0 < |∏ k ∈ range (n + 1), ((1 : ℝ) / 2 - k)| / (n ! : ℝ) :=
    lt_of_lt_of_le (by positivity) hprod
  have hsumchoose : (∑ j ∈ range (n + 1), (n.choose j : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ = ∑ j ∈ range (n + 1), (1 / (4 * (n : ℝ))) * (n.choose j : ℝ) / n := by
      rw [← sum_div, ← mul_sum, hsumchoose]
      ring
    _ ≤ ∑ j ∈ range (n + 1),
        (|∏ k ∈ range (n + 1), ((1 : ℝ) / 2 - k)| / (n ! : ℝ)) * (n.choose j : ℝ) / n := by
      apply sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)) hnreal.le
    _ < ∑ j ∈ range (n + 1),
        |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)| := by
      apply sum_lt_sum_of_nonempty (by simp)
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [abs_eval_lagrange_basis_nat_half hjn]
      have hjhalfpos : 0 < |(j : ℝ) - 1 / 2| := by
        by_cases hj0 : j = 0
        · subst j; norm_num
        · have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
          rw [abs_of_pos (by linarith)]
          linarith
      have hjhalflt : |(j : ℝ) - 1 / 2| < n := by
        apply abs_lt.mpr
        have hjreal : (j : ℝ) ≤ n := by exact_mod_cast hjn
        have hjnonneg : (0 : ℝ) ≤ j := by positivity
        constructor <;> linarith
      have hjchoose : (0 : ℝ) < n.choose j := by
        exact_mod_cast (Nat.choose_pos hjn)
      exact div_lt_div_of_pos_left (mul_pos hprodpos hjchoose) hjhalfpos hjhalflt

end NLAlib

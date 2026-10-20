import NLAlib.ForMathlib.Analysis.Normed.Algebra.SeriesProducts
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Finite products of geometric series and small geometric corrections

The exact profile sum includes zero arity and ratio zero. The inverse-power
estimate follows from Bernoulli's inequality and does not require a strict
smallness condition on the product of the exponent and ratio.
-/

noncomputable section
set_option autoImplicit false
namespace Real

/-- The genuine sum of a finite geometric profile is the product of the
individual geometric sums, including the empty profile. -/
theorem hasSum_pow_sum_fin {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    HasSum (fun t : Fin N → ℕ => r ^ (∑ j, t j)) ((1 - r)⁻¹ ^ N) := by
  have hs : ∀ j : Fin N, HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ := by
    intro j
    simpa only [one_div] using hasSum_geometric_of_lt_one hr0 hr1
  have hn : ∀ j : Fin N, Summable (fun k : ℕ => ‖r ^ k‖) := by
    intro j
    exact summable_norm_geometric_of_norm_lt_one
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have h := hasSum_list_prod_of_summable_norm (fun _ : Fin N => fun k : ℕ => r ^ k)
    (fun _ : Fin N => (1 - r)⁻¹) hs hn
  simpa only [List.prod_ofFn, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using h

/-- A nonnegative geometric correction whose total linear size is at most
two thirds has inverse-power factor at most three, including power zero. -/
theorem inv_one_sub_pow_le_three {x : ℝ} (hx : 0 ≤ x) (m : ℕ)
    (hsmall : (m : ℝ) * x ≤ 2 / 3) : (1 - x)⁻¹ ^ m ≤ 3 := by
  by_cases hm : m = 0
  · simp [hm]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hxmx : x ≤ (m : ℝ) * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hx]
  have hbase : 1 / 3 ≤ (1 - x) ^ m := by
    have hB := one_add_mul_le_pow (a := -x) (by linarith : -2 ≤ -x) m
    simp only [mul_neg, ← sub_eq_add_neg] at hB
    linarith
  have hpos : 0 < (1 - x) ^ m := lt_of_lt_of_le (by norm_num) hbase
  rw [inv_pow]
  exact ((inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 3)).mpr hbase).trans
    (by norm_num)

end Real

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Finite product lower bounds

A finite union bound controls products of `1-u`, and hence descending factorials
without the exponential loss of replacing every factor by one half.
-/
noncomputable section
open Finset
namespace NLAlib

/-- If each `u_i` lies in `[0,1]`, the product of `1-u_i` is at least one minus
their sum. Source: finite union bound; product estimate in the focused BV reroute. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu0 : ∀ i ∈ s, 0 ≤ u i) (hu1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hsi0 (j : ι) (hj : j ∈ s) := hu0 j (mem_insert_of_mem hj)
    have hsi1 (j : ι) (hj : j ∈ s) := hu1 j (mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, u j := sum_nonneg hsi0
    have hmul := mul_le_mul_of_nonneg_left (ih hsi0 hsi1)
      (sub_nonneg.mpr (hu1 i (mem_insert_self _ _)))
    have hui0 := hu0 i (mem_insert_self _ _)
    nlinarith

/-- Casting a descending factorial gives the real product of its descending factors.
Source: Mathlib's descending-factorial product formula; BV coefficient-denominator bridge. -/
theorem cast_descFactorial_eq_prod_range_sub (k m : ℕ) (hm : m ≤ k + 1) :
    (k.descFactorial m : ℝ) = ∏ j ∈ range m, ((k : ℝ) - j) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply prod_congr rfl
  intro j hj
  exact Nat.cast_sub (by have h := mem_range.mp hj; omega)

/-- A descending factorial is bounded below by the corresponding power times
`1-ν(ν+1)/(2k)`. Source: focused BV reroute, finite-product envelope lemma. -/
theorem pow_mul_one_sub_le_cast_descFactorial {k ν : ℕ} (hk : ν < k) :
    (k : ℝ) ^ (ν + 1) * (1 - ((ν : ℝ) * (ν + 1) / 2) / k) ≤
      (k.descFactorial (ν + 1) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum : (∑ j ∈ range (ν + 1), (j : ℝ)) = (ν : ℝ) * (ν + 1) / 2 := by
    have h := sum_range_id_mul_two (ν + 1)
    simp only [Nat.add_sub_cancel] at h
    have hR := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hR
    linarith
  have h := one_sub_sum_le_prod_one_sub (range (ν + 1)) (fun j => (j : ℝ) / k)
    (fun j hj => div_nonneg (Nat.cast_nonneg j) hk0.le)
    (fun j hj => (div_le_one hk0).mpr (by exact_mod_cast (show j ≤ k by
      have h := mem_range.mp hj
      omega)))
  rw [← sum_div, hsum] at h
  have hprod : (∏ j ∈ range (ν + 1), ((k : ℝ) - j)) =
      (k : ℝ) ^ (ν + 1) * ∏ j ∈ range (ν + 1), (1 - (j : ℝ) / k) := by
    calc
      _ = (∏ j ∈ range (ν + 1), (k : ℝ) * (1 - (j : ℝ) / k)) := by
        apply prod_congr rfl
        intro j hj
        field_simp
      _ = _ := by rw [prod_mul_distrib, prod_const, card_range]
  rw [cast_descFactorial_eq_prod_range_sub k (ν + 1) (by omega), hprod]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hk0.le _)

end NLAlib

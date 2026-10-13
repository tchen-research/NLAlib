import Mathlib.Analysis.PSeries

/-! # Explicit positive inverse-power sum bound

The positive inverse-square telescope bounds every inverse-power series of
integer order at least two by two.
-/
noncomputable section
open Finset
namespace NLAlib

/-- The positive inverse-power series of order at least two sums to at most two.
Source: the finite inverse-square telescope used by the focused quadrature reroute. -/
theorem tsum_inv_pow_nat_succ_le_two {p : ℕ} (hp : 2 ≤ p) :
    (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) ^ p)⁻¹) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun j => by positivity)
  intro m
  calc
    _ ≤ ∑ j ∈ range m, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply sum_le_sum
      intro j hj
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ j + 1 by omega)) hp
    _ = ∑ j ∈ Ioo 0 (m + 1), ((j : ℝ) ^ 2)⁻¹ := by
      rw [show Ioo 0 (m + 1) = Ico 1 (m + 1) by ext j; simp; omega,
        sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_comm 1]
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))

end NLAlib

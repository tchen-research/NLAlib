import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv

/-!
# Finite reciprocal exponents from positive weights

These are finite positive-weight identities over the real and extended
nonnegative real numbers. They do not use matrix data. The total divided by
each positive length is at least one, and the reciprocals sum to one.
-/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace Real

/-- Positive real lengths with positive total give ratios at least one and an
exact reciprocal-sum identity. No nonempty-index assumption is needed. -/
theorem one_le_div_and_sum_inv_div_eq_one
    {ι : Type*} [Fintype ι] (s : ι → ℝ) {L : ℝ}
    (hL : ∑ j, s j = L) (hLpos : 0 < L) (hs : ∀ j, 0 < s j) :
    (∀ j, 1 ≤ L / s j) ∧ ∑ j, 1 / (L / s j) = 1 := by
  constructor
  · intro j
    apply (one_le_div (hs j)).mpr
    rw [← hL]
    exact Finset.single_le_sum (fun i _ => (hs i).le) (Finset.mem_univ j)
  · simp_rw [one_div_div]
    rw [← Finset.sum_div, hL, div_self hLpos.ne']

end Real

namespace ENNReal

/-- Coercing positive total/length ratios to extended exponents preserves
both the lower bound one and the exact reciprocal-toReal sum. -/
theorem one_le_ofReal_div_and_sum_inv_toReal_eq_one
    {ι : Type*} [Fintype ι] (s : ι → ℝ) {L : ℝ}
    (hL : ∑ j, s j = L) (hLpos : 0 < L) (hs : ∀ j, 0 < s j) :
    (∀ j, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (L / s j)) ∧
      ∑ j, ((ENNReal.ofReal (L / s j))⁻¹).toReal = 1 := by
  obtain ⟨hp, hsum⟩ := Real.one_le_div_and_sum_inv_div_eq_one s hL hLpos hs
  have hp0 (j : ι) : 0 ≤ L / s j := le_trans zero_le_one (hp j)
  constructor
  · intro j
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hp j)
  · simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hp0 _), one_div] using hsum

end ENNReal

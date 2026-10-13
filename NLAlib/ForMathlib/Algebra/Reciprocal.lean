import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A number plus its reciprocal on the positive half-line

The elementary radius comparison used for Bernstein ellipse geometry.
-/

noncomputable section

namespace NLAlib

/-- `r + r⁻¹` is strictly increasing for `r≥1`.
Source: elementary field algebra; operator derivations §4, helper for
`bernstein-ellipse-def`. -/
theorem strictMonoOn_add_inv_Ici_one {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    StrictMonoOn (fun r : 𝕜 => r + r⁻¹) (Set.Ici 1) := by
  intro r hr s hs hrs
  change 1 ≤ r at hr
  change 1 ≤ s at hs
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs0 : 0 < s := hr0.trans hrs
  have hrsprod : 1 < r * s := by nlinarith
  have hid : s + s⁻¹ - (r + r⁻¹) = (s - r) * (r * s - 1) / (r * s) := by
    field_simp
    ring
  rw [← sub_pos, hid]
  exact div_pos (mul_pos (sub_pos.mpr hrs) (sub_pos.mpr hrsprod)) (mul_pos hr0 hs0)

end NLAlib

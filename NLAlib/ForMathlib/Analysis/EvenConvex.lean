import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Group.EvenFunction

/-! # Even convex real functions are increasing on the nonnegative half-line -/

open Set

/-- A convex even real function is nondecreasing on the nonnegative half-line.
Writing `x` as a convex combination of `y` and `-y` gives the result. -/
theorem ConvexOn.monotoneOn_nonneg_of_even {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (he : Function.Even f) : MonotoneOn f (Ici 0) := by
  intro x hx y hy hxy
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := le_antisymm (hxy.trans_eq hy0) hx
    simp [hx0, hy0]
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have ha : 0 ≤ (y + x) / (2 * y) :=
      div_nonneg (add_nonneg hyp.le hx) (by positivity)
    have hb : 0 ≤ (y - x) / (2 * y) := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
    have hab : (y + x) / (2 * y) + (y - x) / (2 * y) = 1 := by field_simp; ring
    have harg : (y + x) / (2 * y) * y + (y - x) / (2 * y) * (-y) = x := by field_simp; ring
    have h := hf.2 (mem_univ y) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul, harg, he y, ← add_mul, hab, one_mul] at h
    exact h

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact optimization of weighted square perturbation estimates -/

noncomputable section
set_option autoImplicit false

/-- A family of genuine weighted-square estimates gives the sharp additive
perturbation bound. All zero cases are retained, without division by a
possibly vanishing rooted moment. -/
theorem le_add_of_forall_sq_le_weighted_sq {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (h : ∀ ε : ℝ, 0 < ε → a ^ 2 ≤ (1+ε)*b^2 + (1+ε⁻¹)*d^2) :
    a ≤ b+d := by
  by_contra hbad
  have hgap : b+d < a := lt_of_not_ge hbad
  by_cases hbzero : b=0
  · subst b
    by_cases hdzero : d=0
    · subst d
      have hh := h 1 zero_lt_one
      norm_num at hh
      nlinarith
    · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hdzero)
      have hu : 0 < a^2-d^2 := by nlinarith
      let ε := 2*d^2/(a^2-d^2)
      have he : 0 < ε := by dsimp [ε]; positivity
      have hh := h ε he
      have hi : ε⁻¹*d^2 = (a^2-d^2)/2 := by
        dsimp [ε]
        field_simp [hdp.ne',hu.ne']
      nlinarith
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    by_cases hdzero : d=0
    · subst d
      have hu : 0 < a^2-b^2 := by nlinarith
      let ε := (a^2-b^2)/(2*b^2)
      have he : 0 < ε := by dsimp [ε]; positivity
      have hh := h ε he
      have hi : ε*b^2 = (a^2-b^2)/2 := by
        dsimp [ε]
        field_simp [hbp.ne']
      nlinarith
    · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hdzero)
      have hh := h (d/b) (div_pos hdp hbp)
      have hi : (d/b)*b^2 = b*d := by field_simp [hbp.ne']
      have hj : (d/b)⁻¹*d^2 = b*d := by field_simp [hbp.ne',hdp.ne']
      nlinarith

end

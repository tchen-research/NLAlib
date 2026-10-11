import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exact Bernstein exponential parameter

The positive parameter `t/(v+Lt/3)` is admissible, including `L=0`, and its exponent
is exactly `-t²/(2(v+Lt/3))`.
-/

noncomputable section

namespace NLAlib

/-- The actual optimizing parameter is positive, satisfies `θL<3`, and gives the exact
Bernstein exponent. Source: Tropp 2011, Theorem 1.2; operator rederivations
`thm:freedman`, parameter substitution. Atlas `matrix-freedman` (partial). -/
theorem exists_pos_mul_lt_three_bernstein_exponent_eq {t v L : ℝ}
    (ht : 0 < t) (hv : 0 < v) (hL : 0 ≤ L) :
    ∃ θ : ℝ, 0 < θ ∧ θ * L < 3 ∧
      -θ * t + ((θ ^ 2 / 2) / (1 - θ * L / 3)) * v = -(t ^ 2 / (2 * (v + L * t / 3))) := by
  have hden : 0 < v + L * t / 3 := add_pos_of_pos_of_nonneg hv (by positivity)
  let θ := t / (v + L * t / 3)
  have hθ : 0 < θ := div_pos ht hden
  have hθL : θ * L < 3 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  refine ⟨θ, hθ, hθL, ?_⟩
  have hgden : 0 < 1 - θ * L / 3 := by linarith
  field_simp [hden.ne', hgden.ne']
  dsimp [θ]
  field_simp [hden.ne']
  ring

end NLAlib

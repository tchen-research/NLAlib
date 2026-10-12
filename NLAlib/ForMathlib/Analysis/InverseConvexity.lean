import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar reciprocal Jensen gap

The exact nonnegative gap for a positive affine scalar combination gives
strict inverse convexity. Source: Horn--Johnson (2013), Section 7.8;
supports `log-det-concavity`.
-/

noncomputable section
namespace NLAlib

/-- The reciprocal Jensen gap with one endpoint normalized to one is the
positive square expression. Horn--Johnson (2013), Section 7.8;
helper for strict inverse-trace convexity. -/
theorem affine_inv_sub_inv_affine_eq {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (ht : 0 < t) :
    a + b * t⁻¹ - (a + b * t)⁻¹ = a * b * (t - 1) ^ 2 / (t * (a + b * t)) := by
  have he : 0 < a + b * t := add_pos ha (mul_pos hb ht)
  have hbEq : b = 1 - a := by linarith
  rw [hbEq] at he ⊢
  field_simp
  ring

/-- Reciprocal Jensen is weak for every positive scalar endpoint and strict
unless that endpoint equals one. Horn--Johnson (2013), Section 7.8;
helper for strict inverse-trace convexity. -/
theorem inv_affine_le_affine_inv_and_lt_of_ne {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (ht : 0 < t) :
    (a + b * t)⁻¹ ≤ a + b * t⁻¹ ∧ (t ≠ 1 → (a + b * t)⁻¹ < a + b * t⁻¹) := by
  have hgap := affine_inv_sub_inv_affine_eq ha hb hab ht
  have hden : 0 < t * (a + b * t) := mul_pos ht (add_pos ha (mul_pos hb ht))
  constructor
  · have hn : 0 ≤ a * b * (t - 1) ^ 2 / (t * (a + b * t)) :=
      div_nonneg (mul_nonneg (mul_pos ha hb).le (sq_nonneg _)) hden.le
    linarith
  · intro ht1
    have hn : 0 < a * b * (t - 1) ^ 2 / (t * (a + b * t)) :=
      div_pos (mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr ht1))) hden
    linarith

end NLAlib

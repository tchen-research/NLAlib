import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bisection of a strictly increasing real function

The actual midpoint recursion retains a known root and halves the bracket width
at every step. The lower endpoint may be outside the function's open domain:
only interior midpoints are evaluated. This supports singular-edge threshold
equations, including the scree-threshold root.
-/

noncomputable section

open Set

namespace NLAlib

/-- Midpoint bisection for the equation `f x = v`, with the lower half retained
when the midpoint value is at least `v`. -/
def bisectionInterval (f : ℝ → ℝ) (v lo hi : ℝ) : ℕ → ℝ × ℝ
  | 0 => (lo, hi)
  | n + 1 =>
    let p := bisectionInterval f v lo hi n
    let mid := (p.1 + p.2) / 2
    if f mid < v then (mid, p.2) else (p.1, mid)

/-- Each bisection step halves the interval width, independently of the
comparison oracle and without any regularity assumptions on `f`. -/
theorem bisectionInterval_sub (f : ℝ → ℝ) (v lo hi : ℝ) (n : ℕ) :
    (bisectionInterval f v lo hi n).2 - (bisectionInterval f v lo hi n).1 =
      (hi - lo) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [bisectionInterval]
  | succ n ih =>
    simp only [bisectionInterval]
    split_ifs <;> dsimp <;> rw [pow_succ] <;> rw [div_mul_eq_div_div] <;> rw [← ih] <;> ring

/-- Bisection preserves a root of a strictly increasing function on `(a,∞)`.
The initial lower endpoint is allowed to be exactly `a`; every midpoint lies
strictly above `a`, so the recursion never queries a singular endpoint. -/
theorem bisectionInterval_contains_root {f : ℝ → ℝ} {a v lo hi root : ℝ}
    (hf : StrictMonoOn f (Ioi a)) (hroot : f root = v)
    (ha : a ≤ lo) (hlo : lo < root) (hhi : root ≤ hi) (n : ℕ) :
    a ≤ (bisectionInterval f v lo hi n).1 ∧
      (bisectionInterval f v lo hi n).1 < root ∧
      root ≤ (bisectionInterval f v lo hi n).2 := by
  induction n with
  | zero => exact ⟨ha, hlo, hhi⟩
  | succ n ih =>
    let p := bisectionInterval f v lo hi n
    have hp : a ≤ p.1 ∧ p.1 < root ∧ root ≤ p.2 := ih
    have hmid : a < (p.1 + p.2) / 2 := by linarith [hp.1, hp.2.1, hp.2.2]
    have hroota : a < root := lt_of_le_of_lt ha hlo
    have htest : f ((p.1 + p.2) / 2) < v ↔ (p.1 + p.2) / 2 < root := by
      rw [← hroot]
      exact hf.lt_iff_lt hmid hroota
    change a ≤ (if f ((p.1 + p.2) / 2) < v then ((p.1 + p.2) / 2, p.2)
      else (p.1, (p.1 + p.2) / 2)).1 ∧
      (if f ((p.1 + p.2) / 2) < v then ((p.1 + p.2) / 2, p.2)
      else (p.1, (p.1 + p.2) / 2)).1 < root ∧
      root ≤ (if f ((p.1 + p.2) / 2) < v then ((p.1 + p.2) / 2, p.2)
      else (p.1, (p.1 + p.2) / 2)).2
    split_ifs with h
    · exact ⟨hmid.le, htest.mp h, hp.2.2⟩
    · exact ⟨hp.1, hp.2.1, le_of_not_gt (fun hlt => h (htest.mpr hlt))⟩

/-- The computed upper endpoint is within the exact bisection width of the
root. This statement covers a root at the initial upper endpoint. -/
theorem bisectionInterval_upper_sub_root_le {f : ℝ → ℝ} {a v lo hi root : ℝ}
    (hf : StrictMonoOn f (Ioi a)) (hroot : f root = v)
    (ha : a ≤ lo) (hlo : lo < root) (hhi : root ≤ hi) (n : ℕ) :
    0 ≤ (bisectionInterval f v lo hi n).2 - root ∧
      (bisectionInterval f v lo hi n).2 - root ≤ (hi - lo) / (2 : ℝ) ^ n := by
  obtain ⟨_, hl, hu⟩ := bisectionInterval_contains_root hf hroot ha hlo hhi n
  constructor
  · exact sub_nonneg.mpr hu
  · rw [← bisectionInterval_sub f v lo hi n]
    linarith

end NLAlib

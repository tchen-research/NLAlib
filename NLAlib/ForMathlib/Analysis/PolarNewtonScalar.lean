import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Positive scalar Newton iteration for the polar factor

The Cayley coordinate squares at each step, giving the exact iterate and
its double-exponential error bound. Source: Higham (1986), §3.2.
-/
noncomputable section
open Filter
open scoped Topology
namespace NLAlib

/-- The positive scalar Newton recurrence in each fixed singular direction. -/
def polarNewtonScalar (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => (polarNewtonScalar s k + (polarNewtonScalar s k)⁻¹) / 2

/-- Positivity is preserved by every scalar Newton step. -/
theorem polarNewtonScalar_pos {s : ℝ} (hs : 0 < s) (k : ℕ) :
    0 < polarNewtonScalar s k := by
  induction k with
  | zero => exact hs
  | succ k ih => dsimp only [polarNewtonScalar]; positivity

/-- The Cayley coordinate of a positive number lies strictly between minus
one and one. -/
theorem abs_cayley_lt_one {s : ℝ} (hs : 0 < s) : |(s - 1) / (s + 1)| < 1 := by
  rw [abs_div, abs_of_pos (by linarith : 0 < s + 1), div_lt_one (by linarith)]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A scalar Newton step squares its Cayley coordinate exactly. -/
theorem cayley_polarNewton_step {s : ℝ} (hs : 0 < s) :
    (((s + s⁻¹) / 2) - 1) / (((s + s⁻¹) / 2) + 1) = ((s - 1) / (s + 1)) ^ 2 := by
  have hs0 : s ≠ 0 := hs.ne'
  have hp : s + 1 ≠ 0 := by linarith
  have hd : (s + s⁻¹) / 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The Cayley coordinate of the actual recurrence is its initial coordinate
raised to `2^k`. -/
theorem cayley_polarNewtonScalar {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (polarNewtonScalar s k - 1) / (polarNewtonScalar s k + 1) =
      ((s - 1) / (s + 1)) ^ (2 ^ k) := by
  induction k with
  | zero => simp [polarNewtonScalar]
  | succ k ih =>
    rw [polarNewtonScalar, cayley_polarNewton_step (polarNewtonScalar_pos hs k), ih,
      ← pow_mul, pow_succ]

/-- Exact closed form of every scalar iterate, including the initial value.
Higham (1986), equations (3.4)–(3.7).
atlas: polar-newton-iteration (partial) -/
theorem polarNewtonScalar_eq {s : ℝ} (hs : 0 < s) (k : ℕ) :
    polarNewtonScalar s k =
      (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
        (1 - ((s - 1) / (s + 1)) ^ (2 ^ k)) := by
  rw [← cayley_polarNewtonScalar hs k]
  have hp := polarNewtonScalar_pos hs k
  have hd : polarNewtonScalar s k + 1 ≠ 0 := by linarith
  have hn : 1 - (polarNewtonScalar s k - 1) / (polarNewtonScalar s k + 1) ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hd]
    intro h
    linarith
  field_simp
  ring

/-- Every positive scalar starting point converges to one. -/
theorem tendsto_polarNewtonScalar {s : ℝ} (hs : 0 < s) :
    Tendsto (polarNewtonScalar s) atTop (𝓝 1) := by
  have hc : ‖(s - 1) / (s + 1)‖ < 1 := abs_cayley_lt_one hs
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add ht).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)
    (by norm_num : (1 : ℝ) - 0 ≠ 0))
  have he : (fun k => (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
      (1 - ((s - 1) / (s + 1)) ^ (2 ^ k))) = polarNewtonScalar s := by
    funext k
    exact (polarNewtonScalar_eq hs k).symm
  have hlim' : Tendsto (fun k => (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
      (1 - ((s - 1) / (s + 1)) ^ (2 ^ k))) atTop (𝓝 1) := by
    convert hlim using 1
    · funext k; rfl
    · norm_num
  rwa [he] at hlim'

/-- Uniform explicit Newton error for any bound on the initial Cayley coordinate.
The bound retains the denominator needed at the initial iteration.
Higham (1986), §3.2.
atlas: polar-newton-iteration (partial) -/
theorem abs_polarNewtonScalar_sub_one_le {s r : ℝ} (hs : 0 < s)
    (hr : 0 ≤ r) (hr1 : r < 1) (hcr : |(s - 1) / (s + 1)| ≤ r) (k : ℕ) :
    |polarNewtonScalar s k - 1| ≤ 2 * r ^ (2 ^ k) / (1 - r ^ (2 ^ k)) := by
  let c := ((s - 1) / (s + 1)) ^ (2 ^ k)
  have hrp : r ^ (2 ^ k) < 1 := pow_lt_one₀ hr hr1 (by positivity)
  have hcp : |c| ≤ r ^ (2 ^ k) := by
    simpa only [c, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hcr (2 ^ k)
  have hden : 0 < 1 - c := by have := le_abs_self c; linarith
  have he : polarNewtonScalar s k - 1 = 2 * c / (1 - c) := by
    rw [polarNewtonScalar_eq hs]
    change (1 + c) / (1 - c) - 1 = _
    field_simp
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hden]
  apply div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg hr _))
    (mul_le_mul_of_nonneg_left hcp (by norm_num)) (by linarith)
  have := le_abs_self c
  linarith

end NLAlib

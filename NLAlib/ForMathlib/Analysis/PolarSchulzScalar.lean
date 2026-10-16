import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Scalar Newton–Schulz iteration on the polar interval

The first step maps `(0,sqrt 3)` into `(0,1]`; only subsequent steps satisfy
the defect-squaring bound. Source: Higham–Schreiber (1990), §3.
-/
noncomputable section
open Filter
open scoped Topology
namespace NLAlib

/-- The inverse-free scalar polar iteration. -/
def polarSchulzScalar (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => polarSchulzScalar s k * (3 - polarSchulzScalar s k ^ 2) / 2

/-- The exact scalar identity proving that each admissible step is at most one. -/
theorem one_sub_polarSchulz_step (s : ℝ) :
    1 - s * (3 - s ^ 2) / 2 = (s - 1) ^ 2 * (s + 2) / 2 := by ring

/-- One admissible step enters the positive unit interval. -/
theorem polarSchulz_step_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) :
    0 < s * (3 - s ^ 2) / 2 ∧ s * (3 - s ^ 2) / 2 ≤ 1 := by
  constructor
  · positivity
  · have h := one_sub_polarSchulz_step s
    have hn : 0 ≤ (s - 1) ^ 2 * (s + 2) / 2 := by positivity
    linarith

/-- Every iterate after the first lies in `(0,1]`, with no restriction that
the initial defect have norm below one. -/
theorem polarSchulzScalar_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    0 < polarSchulzScalar s (k + 1) ∧ polarSchulzScalar s (k + 1) ≤ 1 := by
  induction k with
  | zero => exact polarSchulz_step_mem hs hs3
  | succ k ih =>
    apply polarSchulz_step_mem ih.1
    nlinarith [sq_nonneg (polarSchulzScalar s (k + 1) - 1)]

/-- Exact scalar orthogonality-defect recurrence. -/
theorem one_sub_sq_polarSchulz_step (s : ℝ) :
    1 - (s * (3 - s ^ 2) / 2) ^ 2 = (1 - s ^ 2) ^ 2 * (3 + (1 - s ^ 2)) / 4 := by
  ring

/-- Positive unit-interval iterates have defects in `[0,1)`. -/
theorem polarSchulzScalar_defect_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    0 ≤ 1 - polarSchulzScalar s (k + 1) ^ 2 ∧
      1 - polarSchulzScalar s (k + 1) ^ 2 < 1 := by
  obtain ⟨hp, hle⟩ := polarSchulzScalar_mem hs hs3 k
  constructor <;> nlinarith [sq_pos_of_pos hp]

/-- After the first iteration, each scalar defect is bounded by the square
of its predecessor. Higham–Schreiber (1990), §3. -/
theorem polarSchulzScalar_defect_step_le {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3)
    (k : ℕ) :
    1 - polarSchulzScalar s (k + 2) ^ 2 ≤
      (1 - polarSchulzScalar s (k + 1) ^ 2) ^ 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, polarSchulzScalar,
    one_sub_sq_polarSchulz_step]
  have he := polarSchulzScalar_defect_mem hs hs3 k
  have hm := mul_le_mul_of_nonneg_left (by linarith :
    3 + (1 - polarSchulzScalar s (k + 1) ^ 2) ≤ 4)
      (sq_nonneg (1 - polarSchulzScalar s (k + 1) ^ 2))
  linarith

/-- Double-exponential scalar defect bound, starting with the first defect. -/
theorem polarSchulzScalar_defect_le {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3)
    (k : ℕ) :
    1 - polarSchulzScalar s (k + 1) ^ 2 ≤
      (1 - polarSchulzScalar s 1 ^ 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ (1 - polarSchulzScalar s (k + 1) ^ 2) ^ 2 :=
        polarSchulzScalar_defect_step_le hs hs3 k
      _ ≤ ((1 - polarSchulzScalar s 1 ^ 2) ^ (2 ^ k)) ^ 2 :=
        pow_le_pow_left₀ (polarSchulzScalar_defect_mem hs hs3 k).1 ih 2
      _ = _ := by rw [← pow_mul, Nat.pow_succ]

/-- The scalar distance to one is bounded by the orthogonality defect. -/
theorem abs_polarSchulzScalar_sub_one_le_defect {s : ℝ}
    (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    |polarSchulzScalar s (k + 1) - 1| ≤ 1 - polarSchulzScalar s (k + 1) ^ 2 := by
  obtain ⟨hp, hle⟩ := polarSchulzScalar_mem hs hs3 k
  rw [abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hle)]

/-- The actual inverse-free scalar recurrence converges to one. -/
theorem tendsto_polarSchulzScalar {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) :
    Tendsto (polarSchulzScalar s) atTop (𝓝 1) := by
  obtain ⟨he0, he1⟩ := polarSchulzScalar_defect_mem hs hs3 0
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one he0 he1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have ht : Tendsto (fun k => polarSchulzScalar s (k + 1) - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (abs_polarSchulzScalar_sub_one_le_defect hs hs3 k).trans
      (polarSchulzScalar_defect_le hs hs3 k)) hp
  have hh : Tendsto (fun k => polarSchulzScalar s (k + 1)) atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using ht.add_const 1
  exact (tendsto_add_atTop_iff_nat 1).mp hh

end NLAlib

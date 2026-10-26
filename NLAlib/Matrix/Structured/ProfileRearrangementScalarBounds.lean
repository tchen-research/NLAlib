import NLAlib.Matrix.Structured.ProfileRearrangementScales
import Mathlib.Algebra.Field.GeomSum

/-!
# Scalar estimates for the profile blocks

The even Schatten exponent `2^(t+2)` absorbs the `t`th block dimension,
while the logarithmic entry thresholds give summable block fluctuations.
Explicit coarse constants suffice for the universal row-comparison bound.
-/

noncomputable section
namespace NLAlib

/-- Exact logarithm of a previous cutoff. -/
theorem log_profilePreviousCutoff (k : ℕ) :
    Real.log (profilePreviousCutoff k : ℝ) = (2 : ℝ) ^ k * Real.log 2 := by
  simp [profilePreviousCutoff, Real.log_pow]

/-- The logarithm of every previous cutoff is positive. -/
theorem log_profilePreviousCutoff_pos (k : ℕ) :
    0 < Real.log (profilePreviousCutoff k : ℝ) := by
  apply Real.log_pos
  exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) (two_le_profilePreviousCutoff k)

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

/-- The block Schatten factor times the logarithmic threshold is uniformly
bounded; equivalently the displayed quotient is at most four. -/
theorem sqrt_two_pow_div_sqrt_log_previous_le_four (k : ℕ) :
    Real.sqrt ((2 ^ (k + 2) : ℕ) : ℝ) /
      Real.sqrt (Real.log (profilePreviousCutoff k : ℝ)) ≤ 4 := by
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (log_profilePreviousCutoff_pos k))).mpr
  have hp : ((2 ^ (k + 2) : ℕ) : ℝ) ≤
      16 * Real.log (profilePreviousCutoff k : ℝ) := by
    rw [log_profilePreviousCutoff, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    norm_num
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0 : ℝ) ≤ 2 ^ k)]
  have h := Real.sqrt_le_sqrt hp
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
    show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)] at h
  exact h

/-- The dimension of a supporting block is absorbed by the even moment
parameter `p = 2^(t+1)`. -/
theorem profileCutoff_succ_eq_two_pow_two_mul (t : ℕ) :
    profileCutoff (t + 1) = 2 ^ (2 * 2 ^ (t + 1)) := by
  unfold profileCutoff
  rw [show t + 1 + 1 = (t + 1) + 1 by omega, pow_succ]
  congr 1
  omega

/-- Logarithmic thresholds decay geometrically with ratio at most `3/4`. -/
theorem one_div_sqrt_log_previous_le_two_mul_pow (k : ℕ) :
    1 / Real.sqrt (Real.log (profilePreviousCutoff k : ℝ)) ≤ 2 * (3 / 4 : ℝ) ^ k := by
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [half_le_log_two])
  have hinv : 1 / Real.sqrt (2 : ℝ) ≤ 3 / 4 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    have h : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  induction k with
  | zero =>
      simp only [profilePreviousCutoff, pow_zero, pow_one, Nat.cast_ofNat, mul_one]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)))).mpr
      linarith
  | succ k ih =>
      have hlog : Real.log (profilePreviousCutoff (k + 1) : ℝ) =
          2 * Real.log (profilePreviousCutoff k : ℝ) := by
        rw [log_profilePreviousCutoff, log_profilePreviousCutoff, pow_succ]
        ring
      rw [hlog, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← one_div_mul_one_div_rev]
      calc
        _ ≤ (2 * (3 / 4 : ℝ) ^ k) * (3 / 4) := mul_le_mul ih hinv
          (by positivity) (by positivity)
        _ = 2 * (3 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- The sum of all block threshold factors is bounded independently of the
finite truncation level. -/
theorem sum_one_div_sqrt_log_previous_le_eight (L : ℕ) :
    (∑ k ∈ Finset.range L, 1 / Real.sqrt (Real.log (profilePreviousCutoff k : ℝ))) ≤ 8 := by
  have hgeom : (∑ k ∈ Finset.range L, (3 / 4 : ℝ) ^ k) ≤ 4 := by
    rw [geom_sum_eq (by norm_num : (3 / 4 : ℝ) ≠ 1)]
    have hpow : 0 ≤ (3 / 4 : ℝ) ^ L := by positivity
    apply (div_le_iff_of_neg (by norm_num : (3 / 4 : ℝ) - 1 < 0)).mpr
    nlinarith
  calc
    _ ≤ ∑ k ∈ Finset.range L, 2 * (3 / 4 : ℝ) ^ k :=
      Finset.sum_le_sum fun k _ => one_div_sqrt_log_previous_le_two_mul_pow k
    _ = 2 * ∑ k ∈ Finset.range L, (3 / 4 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ 8 := by linarith

end NLAlib

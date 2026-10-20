import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Logarithmic dimension change for the quadratic Hermitian dilation -/

noncomputable section
set_option autoImplicit false
namespace Real

/-- Enlarging the matrix dimension from `d` to `3d` changes the source
logarithmic factor by at most a universal factor three. -/
theorem log_three_mul_rpow_three_quarters_le {d : ℕ} (hd : 2 ≤ d) :
    (Real.log (3 * (d : ℝ))) ^ (3 / 4 : ℝ) ≤
      3 * (Real.log (d : ℝ)) ^ (3 / 4 : ℝ) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hlog0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by linarith)
  have hcube : 3 * (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    have hm := mul_nonneg hdp.le (show 0 ≤ (d : ℝ) ^ 2 - 3 by nlinarith)
    nlinarith
  have hlog : Real.log (3 * (d : ℝ)) ≤ 3 * Real.log (d : ℝ) := by
    have h := Real.log_le_log (show (0 : ℝ) < 3 * (d : ℝ) by positivity) hcube
    rw [Real.log_pow] at h
    exact h
  have h3 : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 := by
    calc
      _ ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  calc
    _ ≤ (3 * Real.log (d : ℝ)) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (by nlinarith)) hlog (by norm_num)
    _ = (3 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (d : ℝ)) ^ (3 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hlog0
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hlog0 _)

end Real

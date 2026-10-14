import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite complex trigonometric growth

Cosine is bounded by the exponential of the absolute imaginary coordinate.
The mean-value theorem along a real segment controls sine, and the double-angle
identity then gives a quadratic bound for `1-cos`.
-/

noncomputable section

open Set

namespace Complex

/-- Complex cosine grows by at most the exponential of the absolute imaginary
coordinate. -/
theorem norm_cos_le_exp_abs_im (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  have h : ‖cos w‖ ≤ (Real.exp (-w.im) + Real.exp w.im) / 2 := by
    rw [cos, norm_div, norm_ofNat]
    refine (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)).trans_eq ?_
    simp only [norm_exp, mul_re, I_re, I_im, mul_zero, mul_one,
      zero_sub, neg_re, neg_im, neg_neg]
  have hp := Real.exp_le_exp.mpr (le_abs_self w.im)
  have hn := Real.exp_le_exp.mpr (neg_le_abs w.im)
  linarith

/-- Complex sine is bounded by its argument norm times the exponential of the
absolute imaginary coordinate. -/
theorem norm_sin_le_norm_mul_exp_abs_im (w : ℂ) :
    ‖sin w‖ ≤ ‖w‖ * Real.exp |w.im| := by
  have hd (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t : ℝ => sin ((t : ℂ) * w))
        (cos ((t : ℂ) * w) * w) (Icc (0 : ℝ) 1) t := by
    have h := (((hasDerivAt_id (t : ℂ)).mul_const w).csin).comp_ofReal
    simpa only [id_eq, one_mul] using h.hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖cos ((t : ℂ) * w) * w‖ ≤ ‖w‖ * Real.exp |w.im| := by
    have him : |((t : ℂ) * w).im| ≤ |w.im| := by
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul,
        abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg w.im) ht.2
    rw [norm_mul]
    calc
      ‖cos ((t : ℂ) * w)‖ * ‖w‖ ≤
          Real.exp |((t : ℂ) * w).im| * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_cos_le_exp_abs_im _) (norm_nonneg _)
      _ ≤ Real.exp |w.im| * ‖w‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr him) (norm_nonneg _)
      _ = ‖w‖ * Real.exp |w.im| := mul_comm _ _
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) hd hb (by simp) (by simp)
  simpa only [ofReal_one, ofReal_zero, one_mul, zero_mul, sin_zero,
    sub_zero, sub_zero, norm_one, mul_one] using h

/-- The departure of complex cosine from one is quadratic in the argument,
with growth controlled only by its imaginary coordinate. -/
theorem norm_one_sub_cos_le_norm_sq_mul_exp_abs_im (w : ℂ) :
    ‖1 - cos w‖ ≤ ‖w‖^2 / 2 * Real.exp |w.im| := by
  have hid : 1 - cos w = 2 * sin (w / 2)^2 := by
    calc
      1 - cos w = 1 - cos (2 * (w / 2)) := by congr 2; ring
      _ = 2 * sin (w / 2)^2 := by rw [cos_two_mul_eq_one_sub]; ring
  have hsin := norm_sin_le_norm_mul_exp_abs_im (w / 2)
  have hsq := pow_le_pow_left₀ (norm_nonneg (sin (w / 2))) hsin 2
  rw [hid, norm_mul, norm_pow, norm_ofNat]
  refine (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_eq ?_
  simp only [norm_div, norm_ofNat, div_ofNat_im, abs_div,
    show |(2 : ℝ)| = 2 by norm_num]
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * (|w.im| / 2) = |w.im| := by ring
  rw [he]
  ring

end Complex

import NLAlib.ForMathlib.Analysis.CotangentBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The odd central-sample correction

A quartic bound absorbs the small log-cosine correction in the central
Chebyshev-root sample when the number of roots is odd.
-/
noncomputable section
open Real Set
namespace NLAlib

/-- Squared cosine is at least `3/4` up to angle `π/6`.
Source: cosine monotonicity and its exact special-angle value. -/
theorem three_div_four_le_cos_sq {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π / 6) :
    (3 / 4 : ℝ) ≤ cos x ^ 2 := by
  have hc := cos_le_cos_of_nonneg_of_le_pi hx (by linarith [pi_pos] : π / 6 ≤ π) hxπ
  have hc0 : 0 ≤ cos (π / 6) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have h := pow_le_pow_left₀ hc0 hc 2
  simpa only [sq_cos_pi_div_six] using h

/-- The tangent excess is at most `(4/9)x³` up to angle `π/6`.
Source: focused reroutes, the odd central-sample correction; derivative comparison. -/
theorem tan_sub_le_four_mul_cube_div_nine {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π / 6) :
    tan x - x ≤ 4 * x ^ 3 / 9 := by
  let f := fun x : ℝ => tan x - x - 4 * x ^ 3 / 9
  have hc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], by linarith [hx.2, pi_pos]⟩
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) :
      HasDerivAt f (1 / cos x ^ 2 - 1 - 4 * x ^ 2 / 3) x := by
    have h := ((Real.hasDerivAt_tan (hc x hx).ne').sub (hasDerivAt_id x)).sub
      ((((hasDerivAt_id x).pow 3).const_mul 4).div_const 9)
    exact h.congr_deriv (by dsimp only [id_eq]; ring)
  have hn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) :
      1 / cos x ^ 2 - 1 - 4 * x ^ 2 / 3 ≤ 0 := by
    have hsq := three_div_four_le_cos_sq hx.1 hx.2
    have hs := sin_sq_le_sq (x := x)
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * x ^ 2 / 3 by positivity)
    apply sub_nonpos.mpr
    apply (sub_le_iff_le_add).mpr
    rw [div_le_iff₀ (pow_pos (hc x hx) 2)]
    nlinarith [sin_sq_add_cos_sq x]
  have hm : AntitoneOn f (Icc (0 : ℝ) (π / 6)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (π / 6))
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hn x (interior_subset hx))
  have h := hm (by constructor <;> linarith [pi_pos]) ⟨hx, hxπ⟩ hx
  dsimp [f] at h
  norm_num at h
  linarith

/-- The half-angle tangent identity that exposes the odd correction's cancellation.
Source: focused reroutes, elementary double-angle formulas. -/
theorem tan_sub_half_eq_div_two_cos_half_sq {a : ℝ} (ha : 0 ≤ a) (haπ : a ≤ π / 6) :
    tan a - tan (a / 2) = tan a / (2 * cos (a / 2) ^ 2) := by
  have hca : cos a ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).ne'
  have hch : cos (a / 2) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).ne'
  have hsin : sin a = 2 * sin (a / 2) * cos (a / 2) := by
    simpa only [show 2 * (a / 2) = a by ring] using sin_two_mul (a / 2)
  have hcos : cos a = 2 * cos (a / 2) ^ 2 - 1 := by
    simpa only [show 2 * (a / 2) = a by ring] using cos_two_mul (a / 2)
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  field_simp [hca, hch]
  rw [hsin, hcos]
  ring

/-- The odd central-sample correction is at most `2a⁴/27` for `a≤π/6`.
Source: focused reroutes, the exact odd-sample correction calculation. -/
theorem neg_log_cos_sub_mul_tan_half_le_quartic {a : ℝ} (ha : 0 ≤ a) (haπ : a ≤ π / 6) :
    -log (cos a) - a * tan (a / 2) ≤ 2 * a ^ 4 / 27 := by
  let E := fun x : ℝ => -log (cos x) - x * tan (x / 2)
  let f := fun x : ℝ => E x - 2 * x ^ 4 / 27
  have hc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) : 0 < cos x ∧ 0 < cos (x / 2) := by
    constructor <;> apply cos_pos_of_mem_Ioo <;> constructor <;> linarith [hx.1, hx.2, pi_pos]
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) :
      HasDerivAt E ((tan x - x) / (2 * cos (x / 2) ^ 2)) x := by
    have hlog := ((Real.hasDerivAt_log (hc x hx).1.ne').comp x (Real.hasDerivAt_cos x)).neg
    have htan := (Real.hasDerivAt_tan (hc x hx).2.ne').comp x ((hasDerivAt_id x).div_const 2)
    have h := hlog.sub ((hasDerivAt_id x).mul htan)
    apply h.congr_deriv
    simp only [id_eq, Function.comp_def, one_mul, mul_neg, neg_neg]
    rw [show (cos x)⁻¹ * sin x = tan x by rw [tan_eq_sin_div_cos]; ring]
    rw [show tan x - (tan (x / 2) + x * (1 / cos (x / 2) ^ 2 * (1 / 2))) =
      (tan x - tan (x / 2)) - x * (1 / cos (x / 2) ^ 2 * (1 / 2)) by ring,
      tan_sub_half_eq_div_two_cos_half_sq hx.1 hx.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) :
      (tan x - x) / (2 * cos (x / 2) ^ 2) ≤ 8 * x ^ 3 / 27 := by
    have htan := tan_sub_le_four_mul_cube_div_nine hx.1 hx.2
    have hsq := three_div_four_le_cos_sq (x := x / 2) (by linarith [hx.1]) (by linarith [hx.1, hx.2])
    rw [div_le_iff₀ (mul_pos (by norm_num) (pow_pos (hc x hx).2 2))]
    have hmul := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 16 * x ^ 3 / 27 from div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx.1 _)) (by norm_num))
    nlinarith
  have hdf (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (π / 6)) :
      HasDerivAt f ((tan x - x) / (2 * cos (x / 2) ^ 2) - 8 * x ^ 3 / 27) x := by
    have h := (hd x hx).sub ((((hasDerivAt_id x).pow 4).const_mul 2).div_const 27)
    exact h.congr_deriv (by dsimp only [id_eq]; ring)
  have hm : AntitoneOn f (Icc (0 : ℝ) (π / 6)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (π / 6))
      (fun x hx => (hdf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hdf x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => sub_nonpos.mpr (hb x (interior_subset hx)))
  have h := hm (by constructor <;> linarith [pi_pos]) ⟨ha, haπ⟩ ha
  dsimp [f, E] at h
  norm_num at h
  linarith

end NLAlib

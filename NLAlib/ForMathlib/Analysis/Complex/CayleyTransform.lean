import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Cayley coordinates for the upper half plane

The rational maps identify the complex unit disk and the open upper half
plane. Their exact kernel identity transports the finite-circle Herglotz
representation to real-line Stieltjes kernels.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, scalar Herglotz bridge.
-/

noncomputable section
open Metric Set
namespace Complex

/-- The Cayley map from the upper half plane to the unit disk. -/
def cayleyTransform (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley map from the unit disk to the upper half plane. -/
def inverseCayleyTransform (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The upper-half-plane Cayley denominator does not vanish. -/
theorem add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at hi
  linarith

/-- The inverse Cayley denominator does not vanish inside the disk. -/
theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp only [he, norm_one, lt_self_iff_false] at hw

/-- The Cayley map sends each point of the upper half plane into the disk. -/
theorem norm_cayleyTransform_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖cayleyTransform z‖ < 1 := by
  have hd : 0 < normSq (z + I) := normSq_pos.mpr (add_I_ne_zero_of_im_pos hz)
  have hs : normSq (cayleyTransform z) < 1 := by
    rw [cayleyTransform, normSq_div, div_lt_one hd]
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, I_re, I_im]
    nlinarith
  rw [normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cayleyTransform z)]

/-- The imaginary part of the inverse Cayley map is the disk defect
divided by the squared denominator. -/
theorem im_inverseCayleyTransform (w : ℂ) :
    (inverseCayleyTransform w).im = (1 - normSq w) / normSq (1 - w) := by
  simp only [inverseCayleyTransform, div_im, mul_re, mul_im, add_re, add_im,
    sub_re, sub_im, one_re, one_im, I_re, I_im, normSq_apply]
  ring

/-- The inverse Cayley map has positive imaginary part in the unit disk. -/
theorem im_inverseCayleyTransform_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (inverseCayleyTransform w).im := by
  rw [im_inverseCayleyTransform]
  have hn : normSq w < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  exact div_pos (by linarith) (normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hw))

/-- The inverse Cayley map is analytic throughout the open unit disk. -/
theorem analyticOnNhd_inverseCayleyTransform :
    AnalyticOnNhd ℂ inverseCayleyTransform (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_norm_lt_one hw')

/-- The Cayley map is analytic throughout the open upper half plane. -/
theorem analyticOnNhd_cayleyTransform :
    AnalyticOnNhd ℂ cayleyTransform {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const)
    (add_I_ne_zero_of_im_pos hz)

/-- The finite Cayley image never equals the missing boundary point `1`. -/
theorem one_sub_cayleyTransform_ne_zero {z : ℂ} (hz : z + I ≠ 0) :
    1 - cayleyTransform z ≠ 0 := by
  intro h
  have he : z - I = z + I :=
    (div_eq_one_iff_eq hz).mp (sub_eq_zero.mp h).symm
  have hi := congrArg Complex.im he
  simp only [sub_im, add_im, I_im] at hi
  linarith

/-- The inverse Cayley map recovers each finite upper-half-plane point. -/
theorem inverseCayleyTransform_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    inverseCayleyTransform (cayleyTransform z) = z := by
  apply (div_eq_iff (one_sub_cayleyTransform_ne_zero hz)).mpr
  unfold cayleyTransform
  field_simp [hz]
  ring_nf

/-- The center of the disk corresponds to the upper-half-plane point `i`. -/
@[simp] theorem inverseCayleyTransform_zero : inverseCayleyTransform 0 = I := by
  simp only [inverseCayleyTransform, add_zero, sub_zero, mul_one, div_one]

end Complex

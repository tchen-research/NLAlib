import NLAlib.ForMathlib.Analysis.Complex.Harmonic.HalfPlaneRepresentation
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The mass kernel in upper-half-plane Herglotz normalization

Vertical imaginary arguments give a nonnegative increasing family of
Poisson tests. Their limit is the real-line Stieltjes mass weight; the
exceptional circle point represents mass at infinity.
Source: the Stieltjes normalization used in Ajanki--Erdos--Kruger (2019),
Proposition 2.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology

namespace Complex

/-- The real part of a unit-circle point is at most one. -/
theorem circle_re_le_one (ξ : Circle) : (ξ : ℂ).re ≤ 1 := by
  simpa only [Circle.norm_coe] using re_le_norm (ξ : ℂ)

/-- The real part of a unit-circle point is at least negative one. -/
theorem neg_one_le_circle_re (ξ : Circle) : -1 ≤ (ξ : ℂ).re := by
  have h := abs_re_le_norm (ξ : ℂ)
  rw [Circle.norm_coe] at h
  exact (neg_le_neg h).trans (neg_abs_le _)

/-- Every unit-circle point except `1` has real part strictly below one. -/
theorem circle_re_lt_one_of_ne_one {ξ : Circle} (hξ : ξ ≠ 1) : (ξ : ℂ).re < 1 := by
  apply lt_of_le_of_ne (circle_re_le_one ξ)
  intro he
  have hs := Circle.normSq_coe ξ
  rw [normSq_apply] at hs
  have hi : (ξ : ℂ).im = 0 := by nlinarith [sq_nonneg (ξ : ℂ).im]
  apply hξ
  apply Circle.ext
  apply Complex.ext
  · simpa only [Circle.coe_one, one_re] using he
  · simpa only [Circle.coe_one, one_im] using hi

/-- On the imaginary axis the Cayley coordinate is real. -/
theorem cayleyTransform_mul_I (y : ℝ) (hy : y + 1 ≠ 0) :
    cayleyTransform ((y : ℂ) * I) = (((y - 1) / (y + 1) : ℝ) : ℂ) := by
  simp only [cayleyTransform, ofReal_div, ofReal_sub, ofReal_add, ofReal_one]
  have hd : (y : ℂ) * I + I ≠ 0 := by
    rw [← add_one_mul]
    exact mul_ne_zero (by exact_mod_cast hy) I_ne_zero
  field_simp [hd, hy]

/-- The scalar denominator in the vertical Poisson mass kernel is
strictly positive. -/
theorem circle_mass_denominator_pos (ξ : Circle) {y : ℝ} (hy : 0 < y) :
    0 < (1 - (ξ : ℂ).re) * y ^ 2 + (1 + (ξ : ℂ).re) := by
  have ha : 0 ≤ 1 - (ξ : ℂ).re := sub_nonneg.mpr (circle_re_le_one ξ)
  have hb : 0 ≤ 1 + (ξ : ℂ).re := by linarith [neg_one_le_circle_re ξ]
  by_cases h : 1 - (ξ : ℂ).re = 0
  · have he : (ξ : ℂ).re = 1 := by linarith
    simp only [he, sub_self, zero_mul]
    norm_num
  · have hapos : 0 < 1 - (ξ : ℂ).re := lt_of_le_of_ne ha (Ne.symm h)
    exact add_pos_of_pos_of_nonneg (mul_pos hapos (sq_pos_of_pos hy)) hb

/-- The imaginary-axis Poisson test has a real rational expression whose
limit gives the Stieltjes mass. -/
theorem mul_poissonKernel_cayley_mul_I (ξ : Circle) {y : ℝ} (hy : 0 < y) :
    y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ =
      2 * y ^ 2 / ((1 - (ξ : ℂ).re) * y ^ 2 + (1 + (ξ : ℂ).re)) := by
  have hy1 : y + 1 ≠ 0 := by positivity
  rw [cayleyTransform_mul_I y hy1]
  have hs : (ξ : ℂ).im ^ 2 = 1 - (ξ : ℂ).re ^ 2 := by
    have h := Circle.normSq_coe ξ
    rw [normSq_apply] at h
    nlinarith
  have hkernel : poissonKernel 0 ((((y - 1) / (y + 1) : ℝ) : ℂ)) ξ =
      (1 - ((y - 1) / (y + 1)) ^ 2) /
        (((ξ : ℂ).re - (y - 1) / (y + 1)) ^ 2 + (ξ : ℂ).im ^ 2) := by
    simp only [poissonKernel_def, sub_zero, Circle.norm_coe, one_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, ← normSq_eq_norm_sq, normSq_apply,
      sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, ← sq]
  rw [hkernel, hs]
  have hd := circle_mass_denominator_pos ξ hy
  have hden : ((ξ : ℂ).re - (y - 1) / (y + 1)) ^ 2 + (1 - (ξ : ℂ).re ^ 2) =
      2 * ((1 - (ξ : ℂ).re) * y ^ 2 + (1 + (ξ : ℂ).re)) / (y + 1) ^ 2 := by
    field_simp [hy1]
    ring
  have hnum : 1 - ((y - 1) / (y + 1)) ^ 2 = 4 * y / (y + 1) ^ 2 := by
    field_simp [hy1]
    ring
  rw [hden, hnum]
  field_simp [hy1, hd.ne']
  ring

/-- Vertical Poisson mass tests are nonnegative. -/
theorem mul_poissonKernel_cayley_mul_I_nonneg (ξ : Circle) {y : ℝ} (hy : 0 < y) :
    0 ≤ y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ := by
  rw [mul_poissonKernel_cayley_mul_I ξ hy]
  exact div_nonneg (by positivity) (circle_mass_denominator_pos ξ hy).le

/-- Away from the circle point at infinity, each vertical Poisson mass
test is bounded by the real-line Stieltjes mass weight. -/
theorem mul_poissonKernel_cayley_mul_I_le {ξ : Circle} (hξ : ξ ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ ≤ 2 / (1 - (ξ : ℂ).re) := by
  rw [mul_poissonKernel_cayley_mul_I ξ hy]
  apply (div_le_div_iff₀ (circle_mass_denominator_pos ξ hy)
    (sub_pos.mpr (circle_re_lt_one_of_ne_one hξ))).mpr
  nlinarith [neg_one_le_circle_re ξ]

/-- At the missing boundary point the vertical test is `y²`, encoding
the possible linear term of a general Herglotz function. -/
theorem mul_poissonKernel_cayley_mul_I_one {y : ℝ} (hy : 0 < y) :
    y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) (1 : Circle) = y ^ 2 := by
  rw [mul_poissonKernel_cayley_mul_I _ hy]
  simp only [Circle.coe_one, one_re, sub_self, zero_mul, zero_add]
  ring

/-- Away from the circle point at infinity, the vertical Poisson mass
tests converge to the real-line Stieltjes mass weight. -/
theorem tendsto_mul_poissonKernel_cayley_mul_I {ξ : Circle} (hξ : ξ ≠ 1) :
    Tendsto (fun y : ℝ => y * poissonKernel 0 (cayleyTransform ((y : ℂ) * I)) ξ)
      atTop (𝓝 (2 / (1 - (ξ : ℂ).re))) := by
  have hz : Tendsto (fun y : ℝ => (1 + (ξ : ℂ).re) / y ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (α := ℝ) (show (2 : ℕ) ≠ 0 by decide)).const_div_atTop _
  have ha := sub_pos.mpr (circle_re_lt_one_of_ne_one hξ)
  have ht : Tendsto (fun y : ℝ => 2 / ((1 - (ξ : ℂ).re) + (1 + (ξ : ℂ).re) / y ^ 2))
      atTop (𝓝 (2 / (1 - (ξ : ℂ).re))) := by
    convert! tendsto_const_nhds.div (tendsto_const_nhds.add hz)
      (by simpa only [add_zero] using ha.ne') using 1
    simp only [add_zero]
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [mul_poissonKernel_cayley_mul_I ξ hy]
  field_simp [hy.ne', (circle_mass_denominator_pos ξ hy).ne']

end Complex

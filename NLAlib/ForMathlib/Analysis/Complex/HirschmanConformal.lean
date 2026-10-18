import NLAlib.ForMathlib.Analysis.Complex.HirschmanKernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# An explicit disk-to-strip map for weighted interpolation

The map passes through the upper half-plane and sends the center of the disk
to the interpolation parameter. Its actual boundary parametrization will
identify the explicit Stein--Hirschman weights.
-/

noncomputable section

open Real Set Metric

namespace Complex

/-- The Cayley map with prescribed upper-half-plane center `a + ib`. -/
def hirschmanDiskToHalfPlane (a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) + (b : ℂ) * I * ((1 + z) / (1 - z))

/-- The real part of the basic Cayley quotient. -/
theorem cayleyQuotient_re (z : ℂ) :
    ((1 + z) / (1 - z)).re = (1 - normSq z) / normSq (1 - z) := by
  rw [div_re]
  simp only [add_re, sub_re, one_re, add_im, sub_im, one_im, zero_add, zero_sub, normSq_apply]
  ring

/-- The imaginary part records positivity on the disk exactly. -/
theorem hirschmanDiskToHalfPlane_im (a b : ℝ) (z : ℂ) :
    (hirschmanDiskToHalfPlane a b z).im = b * (1 - normSq z) / normSq (1 - z) := by
  simp only [hirschmanDiskToHalfPlane, add_im, ofReal_im, zero_add, mul_im, mul_re,
    ofReal_re, I_im, I_re, mul_one, mul_zero, zero_mul, sub_zero, add_zero]
  rw [cayleyQuotient_re]
  ring

/-- The entire open unit disk maps into the upper half-plane. -/
theorem hirschmanDiskToHalfPlane_im_pos (a : ℝ) {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < (hirschmanDiskToHalfPlane a b z).im := by
  have hzn : ‖z‖ < 1 := by simpa using hz
  have hz1 : z ≠ 1 := by intro h; subst z; simp at hzn
  have hden : 0 < normSq (1 - z) := normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hnum : 0 < 1 - normSq z := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [hirschmanDiskToHalfPlane_im]
  exact div_pos (mul_pos hb hnum) hden

/-- The explicit logarithmic map to the vertical strip `0 < Re z < 1`. -/
def hirschmanDiskToStrip (r : ℝ) (z : ℂ) : ℂ :=
  log (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) z) * (-I) / (π : ℂ)

/-- Its real part is the normalized half-plane argument. -/
theorem hirschmanDiskToStrip_re (r : ℝ) (z : ℂ) :
    (hirschmanDiskToStrip r z).re =
      arg (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) z) / π := by
  simp [hirschmanDiskToStrip, div_ofReal_re, mul_re, log_im]

/-- Every point of the open disk maps strictly inside the vertical strip. -/
theorem hirschmanDiskToStrip_re_mem_Ioo {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : (hirschmanDiskToStrip r z).re ∈ Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have him := hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs hz
  rw [hirschmanDiskToStrip_re]
  constructor
  · apply div_pos _ pi_pos
    exact lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) (by
      intro h
      exact him.ne' (arg_eq_zero_iff.mp h.symm).2)
  · apply (div_lt_one pi_pos).2
    exact arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))

/-- The disk center maps to precisely the prescribed interpolation parameter. -/
theorem hirschmanDiskToStrip_zero {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    hirschmanDiskToStrip r 0 = (r : ℂ) := by
  have hcenter : hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) 0 =
      exp (((π * r : ℝ) : ℂ) * I) := by
    simp [hirschmanDiskToHalfPlane, exp_mul_I]
  unfold hirschmanDiskToStrip
  rw [hcenter, log_exp (by simp; nlinarith [pi_pos, hr.1]) (by simp; nlinarith [pi_pos, hr.2])]
  simp only [ofReal_mul]
  field_simp
  simp [I_sq]

/-- The disk-to-strip map is holomorphic throughout the actual open unit disk. -/
theorem differentiableAt_hirschmanDiskToStrip {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ (hirschmanDiskToStrip r) z := by
  have hzn : ‖z‖ < 1 := by simpa using hz
  have hz1 : z ≠ 1 := by intro h; subst z; simp at hzn
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have him := hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs hz
  have hM : DifferentiableAt ℂ
      (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r))) z := by
    unfold hirschmanDiskToHalfPlane
    fun_prop (disch := exact sub_ne_zero.mpr hz1.symm)
  exact (((differentiableAt_log (Or.inr (ne_of_gt him))).comp z hM).mul_const (-I)).div_const _

theorem analyticOnNhd_hirschmanDiskToStrip {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (hirschmanDiskToStrip r) (ball (0 : ℂ) 1) := by
  apply (analyticOnNhd_iff_differentiableOn isOpen_ball).2
  exact fun z hz => (differentiableAt_hirschmanDiskToStrip hr hz).differentiableWithinAt

end Complex

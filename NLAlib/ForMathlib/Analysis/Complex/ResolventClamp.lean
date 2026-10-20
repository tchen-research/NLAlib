import NLAlib.ForMathlib.Analysis.Complex.ResolventModulus
import Mathlib.Topology.Order.ProjIcc

/-!
# Scalar resolvents under actual symmetric clipping

Clipping a real point to `[-L,L]` changes a purely imaginary resolvent by
at most `1/L`. This is the scalar continuous-functional-calculus input to
one-step compression of an arbitrary deterministic mean.
-/

noncomputable section
set_option autoImplicit false

private theorem Complex.norm_inv_sub_inv_sub_real_le {z : ℂ} (hz : 0 < z.im)
    {L : ℝ} (hL : 0 < L) (x y : ℝ)
    (hnum : |x-y| ≤ ‖z-(x : ℂ)‖) (hden : L ≤ ‖z-(y : ℂ)‖) :
    ‖(z-(x : ℂ))⁻¹-(z-(y : ℂ))⁻¹‖ ≤ L⁻¹ := by
  have hne (t : ℝ) : z-(t : ℂ) ≠ 0 := by
    intro hh
    have ht : z = (t : ℂ) := sub_eq_zero.mp hh
    have : z.im=0 := by rw [ht]; rfl
    exact hz.ne' this
  have hd : dist (z-(x : ℂ)) (z-(y : ℂ)) = |x-y| := by
    rw [dist_eq_norm]
    have he : z-(x : ℂ)-(z-(y : ℂ)) = ((y-x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  rw [← dist_eq_norm,dist_inv_inv₀ (hne x) (hne y),hd]
  have hx : 0 < ‖z-(x : ℂ)‖ := norm_pos_iff.mpr (hne x)
  have hy : 0 < ‖z-(y : ℂ)‖ := hL.trans_le hden
  calc
    _ ≤ ‖z-(x : ℂ)‖ / (‖z-(x : ℂ)‖ * ‖z-(y : ℂ)‖) :=
      div_le_div_of_nonneg_right hnum (mul_pos hx hy).le
    _ = (‖z-(y : ℂ)‖)⁻¹ := by field_simp
    _ ≤ _ := by simpa only [one_div] using one_div_le_one_div_of_le hL hden

/-- Actual scalar resolvents at purely imaginary height differ by at most
`1/L` after projecting the real spectral parameter to `[-L,L]`. -/
theorem Complex.norm_inv_sub_real_sub_inv_sub_clamp_le {z : ℂ}
    (hre : z.re=0) (hz : 0 < z.im) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ‖(z-(x : ℂ))⁻¹-
      (z-((max (-L) (min L x) : ℝ) : ℂ))⁻¹‖ ≤ L⁻¹ := by
  have hreal (t : ℝ) : |t| ≤ ‖z-(t : ℂ)‖ := by
    simpa only [Complex.sub_re,Complex.ofReal_re,hre,zero_sub,abs_neg] using
      Complex.abs_re_le_norm (z-(t : ℂ))
  by_cases hleft : x ≤ -L
  · have he : max (-L) (min L x) = -L := by
      rw [min_eq_right (by linarith),max_eq_left hleft]
    rw [he]
    apply Complex.norm_inv_sub_inv_sub_real_le hz hL x (-L)
    · have hn : x+L ≤ 0 := by linarith
      have hx : x ≤ 0 := by linarith
      calc
        |x- -L| = -(x+L) := by rw [sub_neg_eq_add,abs_of_nonpos hn]
        _ ≤ |x| := by rw [abs_of_nonpos hx]; linarith
        _ ≤ _ := hreal x
    · simpa only [abs_neg,abs_of_pos hL] using hreal (-L)
  by_cases hright : L ≤ x
  · have he : max (-L) (min L x) = L := by
      rw [min_eq_left hright,max_eq_right (by linarith)]
    rw [he]
    apply Complex.norm_inv_sub_inv_sub_real_le hz hL x L
    · have hn : 0 ≤ x-L := sub_nonneg.mpr hright
      have hx : 0 ≤ x := hL.le.trans hright
      calc
        |x-L| = x-L := abs_of_nonneg hn
        _ ≤ |x| := by rw [abs_of_nonneg hx]; linarith
        _ ≤ _ := hreal x
    · simpa only [abs_of_pos hL] using hreal L
  · have he : max (-L) (min L x) = x := by
      rw [min_eq_right (le_of_not_ge hright),max_eq_right (le_of_not_ge hleft)]
    simp only [he,sub_self,norm_zero]
    exact inv_nonneg.mpr hL.le

end

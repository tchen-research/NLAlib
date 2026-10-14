import NLAlib.Polynomial.FunctionApproximation.EllipseGeometry

/-!
# Imaginary-coordinate bounds on Bernstein ellipses

The Joukowski annulus description supplies the minor semiaxis bound, including
ellipse parameter one. Exponential parameters give the usual hyperbolic
semiaxes used in finite polynomial degree transfer.
-/

noncomputable section

open Complex Set

namespace NLAlib

/-- The absolute imaginary part of a filled Bernstein-ellipse point is at most
the minor semiaxis, including the degenerate parameter-one interval. -/
theorem abs_im_le_of_mem_filledBernsteinEllipse {ρ : ℝ} (hρ : 1 ≤ ρ)
    {z : ℂ} (hz : z ∈ filledBernsteinEllipse ρ) : |z.im| ≤ (ρ - ρ⁻¹) / 2 := by
  obtain ⟨w, hw, rfl⟩ := hz
  let r := ‖w‖
  have hr : 0 < r := by change 0 < ‖w‖; linarith [hw.1]
  have hρpos : 0 < ρ := by linarith
  have hi : (joukowski w).im = w.im * ((1 - (r^2)⁻¹) / 2) := by
    rw [joukowski, Complex.div_ofNat_im, Complex.add_im, Complex.inv_im,
      Complex.normSq_eq_norm_sq]
    change (w.im + -w.im / r^2) / 2 = w.im * ((1 - (r^2)⁻¹) / 2)
    field_simp
    ring
  have hc : 0 ≤ (1 - (r^2)⁻¹) / 2 := by
    have hsq : 1 ≤ r^2 := one_le_pow₀ hw.1
    have hinv : (r^2)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hr 2)).mpr hsq
    linarith
  have hinv : ρ⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hρpos hr).mpr hw.2
  have hrange : r - r⁻¹ ≤ ρ - ρ⁻¹ := by
    have hwr : r ≤ ρ := hw.2
    linarith
  rw [hi, abs_mul, abs_of_nonneg hc]
  calc
    |w.im| * ((1 - (r^2)⁻¹) / 2) ≤ r * ((1 - (r^2)⁻¹) / 2) :=
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) hc
    _ = (r - r⁻¹) / 2 := by field_simp
    _ ≤ (ρ - ρ⁻¹) / 2 := div_le_div_of_nonneg_right hrange (by norm_num)

/-- The open Bernstein ellipse with parameter `exp t` has modulus at most
`cosh t` and imaginary-coordinate modulus at most `sinh t`. -/
theorem norm_le_cosh_and_abs_im_le_sinh_of_mem_openBernsteinEllipse {t : ℝ}
    (ht : 0 < t) {z : ℂ} (hz : z ∈ openBernsteinEllipse (Real.exp t)) :
    ‖z‖ ≤ Real.cosh t ∧ |z.im| ≤ Real.sinh t := by
  have hρ : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hfilled := (mem_filledBernsteinEllipse_iff hρ.le z).mpr
    ((mem_openBernsteinEllipse_iff hρ z).mp hz).le
  constructor
  · simpa only [Real.cosh_eq, Real.exp_neg] using norm_le_of_mem_filledBernsteinEllipse hρ.le hfilled
  · simpa only [Real.sinh_eq, Real.exp_neg] using abs_im_le_of_mem_filledBernsteinEllipse hρ.le hfilled

end NLAlib

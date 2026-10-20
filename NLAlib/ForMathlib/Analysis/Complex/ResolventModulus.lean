import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scalar nonreal resolvent modulus is globally Lipschitz

On the real line, a fixed nonreal complex scalar stays at least its imaginary
height away. The inverse-distance identity consequently gives the exact
inverse-height-squared Lipschitz constant for its resolvent modulus. This
is the scalar input to Jackson approximation of self-adjoint resolvents.
-/

noncomputable section
set_option autoImplicit false

/-- The scalar resolvent modulus on the real line has Lipschitz constant
equal to the reciprocal square of the positive imaginary height. -/
theorem Complex.lipschitzWith_norm_inv_sub_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    LipschitzWith ⟨z.im⁻¹ ^ 2, by positivity⟩
      (fun x : ℝ => ‖(z - (x : ℂ))⁻¹‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hheight (t : ℝ) : z.im ≤ ‖z - (t : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hz] using
      Complex.abs_im_le_norm (z - (t : ℂ))
  have hne (t : ℝ) : z - (t : ℂ) ≠ 0 := by
    intro hzero
    have h := hheight t
    rw [hzero, norm_zero] at h
    exact hz.not_ge h
  have hd : dist (z - (x : ℂ)) (z - (y : ℂ)) = dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : z - (x : ℂ) - (z - (y : ℂ)) = ((y - x : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub]
      ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
  have hprod : z.im ^ 2 ≤ ‖z - (x : ℂ)‖ * ‖z - (y : ℂ)‖ := by
    simpa only [pow_two] using mul_le_mul (hheight x) (hheight y) hz.le (norm_nonneg _)
  calc
    _ ≤ dist ((z - (x : ℂ))⁻¹) ((z - (y : ℂ))⁻¹) := by
      simpa only [dist_eq_norm] using dist_norm_norm_le ((z - (x : ℂ))⁻¹) ((z - (y : ℂ))⁻¹)
    _ = dist x y / (‖z - (x : ℂ)‖ * ‖z - (y : ℂ)‖) := by
      rw [dist_inv_inv₀ (hne x) (hne y), hd]
    _ ≤ dist x y / z.im ^ 2 :=
      div_le_div_of_nonneg_left (dist_nonneg) (sq_pos_of_pos hz) hprod
    _ = _ := by
      change dist x y / z.im ^ 2 = z.im⁻¹ ^ 2 * dist x y
      rw [div_eq_mul_inv, inv_pow]
      ring

end

import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import NLAlib.ForMathlib.Algebra.Resolvent

/-!
# Native resolvent continuity in its spectral parameter

The first resolvent identity gives the exact inverse-height product bound,
including the trivial algebra. Fixed-height real parameters have the sharp
inverse-height-square Lipschitz constant.
-/

noncomputable section
set_option autoImplicit false
variable {A : Type*} [CStarAlgebra A]

/-- The actual nonreal self-adjoint resolvent is Lipschitz between spectral
parameters with the product of their reciprocal imaginary heights. -/
theorem IsSelfAdjoint.norm_resolvent_sub_le_of_im_ne_zero
    {a : A} (ha : IsSelfAdjoint a) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖resolvent a z-resolvent a w‖ ≤ ‖z-w‖*(|z.im|⁻¹*|w.im|⁻¹) := by
  rw [spectrum.resolvent_sub_resolvent_eq_sub_smul_mul a
    (ha.isUnit_algebraMap_sub_of_im_ne_zero hz)
    (ha.isUnit_algebraMap_sub_of_im_ne_zero hw), norm_smul, norm_sub_rev w z]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_mul_le _ _).trans
    (mul_le_mul (ha.norm_resolvent_le hz) (ha.norm_resolvent_le hw)
      (norm_nonneg _) (by positivity))

/-- At fixed nonzero imaginary height, the actual norm of a self-adjoint
resolvent has the sharp real-parameter Lipschitz constant `height^(-2)`. -/
theorem IsSelfAdjoint.abs_norm_resolvent_real_sub_le
    {a : A} (ha : IsSelfAdjoint a) (x y : ℝ) {η : ℝ} (hη : η ≠ 0) :
    |‖resolvent a ((x : ℂ)+(η : ℂ)*Complex.I)‖-
      ‖resolvent a ((y : ℂ)+(η : ℂ)*Complex.I)‖| ≤ |x-y|/η^2 := by
  have hz : ((x : ℂ)+(η : ℂ)*Complex.I).im ≠ 0 := by simpa using hη
  have hw : ((y : ℂ)+(η : ℂ)*Complex.I).im ≠ 0 := by simpa using hη
  have hs := (abs_norm_sub_norm_le _ _).trans (ha.norm_resolvent_sub_le_of_im_ne_zero hz hw)
  have he : ((x : ℂ)+(η : ℂ)*Complex.I)-((y : ℂ)+(η : ℂ)*Complex.I) =
      ((x-y : ℝ) : ℂ) := by push_cast; ring
  simp only [he, Complex.norm_real, Real.norm_eq_abs, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hs
  calc
    _ ≤ |x-y| * (|η|⁻¹*|η|⁻¹) := hs
    _ = _ := by rw [← pow_two, inv_pow, sq_abs, div_eq_mul_inv]

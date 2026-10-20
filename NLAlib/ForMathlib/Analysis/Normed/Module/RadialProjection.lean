import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Radial projection to a norm ball

The continuous radial retraction makes an almost-everywhere bounded random
vector globally bounded while keeping its law unchanged. It is defined in
every real normed vector space and does not require an inner product.
-/

noncomputable section
set_option autoImplicit false

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection to the closed ball about zero of positive radius `R`.
For `R = 0` it is zero; at negative radii the displayed scalar formula is used. -/
def radialProj (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

/-- Radial projection at radius zero is the zero map. -/
@[simp] theorem radialProj_zero (x : E) : radialProj 0 x = 0 := by
  simp [radialProj]

/-- Projection fixes every vector already inside the nonnegative-radius ball. -/
theorem radialProj_eq_self {R : ℝ} (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    radialProj R x = x := by
  rcases hR.eq_or_lt with rfl | hR
  · have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
    simp [hx0]
  · simp [radialProj, max_eq_left hx, hR.ne']

/-- The projected vector always has norm at most the nonnegative radius. -/
theorem norm_radialProj_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖radialProj R x‖ ≤ R := by
  rcases hR.eq_or_lt with rfl | hR
  · simp
  have hd : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [radialProj, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hR.le hd.le), div_mul_eq_mul_div]
  exact (div_le_iff₀ hd).mpr
    (mul_le_mul_of_nonneg_left (le_max_right R ‖x‖) hR.le)

/-- Radial projection is continuous, including radius zero. -/
theorem continuous_radialProj {R : ℝ} (hR : 0 ≤ R) :
    Continuous (radialProj R : E → E) := by
  rcases hR.eq_or_lt with rfl | hR
  · have hz : (radialProj 0 : E → E) = fun _ => 0 := funext radialProj_zero
    rw [hz]
    exact continuous_const
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun x => (hR.trans_le (le_max_left R ‖x‖)).ne')).smul continuous_id

end NormedSpace

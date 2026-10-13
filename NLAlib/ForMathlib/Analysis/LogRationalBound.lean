import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A rational lower estimate for the real logarithm

Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Real Set

namespace NLAlib

/-- A rational lower estimate for the logarithm on `[1,∞)`.
Source: differentiation of `log x - 2(x-1)/(x+1)`. -/
theorem two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ log x := by
  let f := fun x : ℝ => log x - 2 * (x - 1) / (x + 1)
  have hd : ∀ x ∈ Ici (1 : ℝ), HasDerivAt f ((x - 1) ^ 2 / (x * (x + 1) ^ 2)) x := by
    intro x hx
    have hx' : 1 ≤ x := hx
    have hx0 : x ≠ 0 := by linarith [hx']
    have hx1 : x + 1 ≠ 0 := by linarith [hx']
    have h := (Real.hasDerivAt_log hx0).sub
      ((((hasDerivAt_id x).sub_const 1).const_mul 2).div ((hasDerivAt_id x).add_const 1) hx1)
    apply h.congr_deriv
    simp only [id_eq]
    field_simp
    ring
  have hm : MonotoneOn f (Ici (1 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => div_nonneg (sq_nonneg _) (mul_nonneg (by have hx' : 1 ≤ x := interior_subset hx; linarith) (sq_nonneg _)))
  have h := hm (by simp) hx hx
  dsimp [f] at h
  rw [log_one] at h
  norm_num at h
  linarith

/-- The constant remainder in the midpoint-cotangent logarithmic estimate is at most one.
Source: focused rederivations, the numerical inequality following `thm:lobatto`. -/
theorem cotangent_log_remainder_le_one : (2 / π) * (2 + log (2 / π)) ≤ 1 := by
  have hp : 0 < π := pi_pos
  have hlo := two_mul_sub_div_add_le_log (x := π / 2) (by linarith [pi_gt_three])
  have hlog : log (2 / π) = -log (π / 2) := by
    rw [show 2 / π = (π / 2)⁻¹ by field_simp, log_inv]
  rw [hlog, div_mul_eq_mul_div, div_le_iff₀ hp]
  have hden : 0 < π / 2 + 1 := by linarith
  have hnum : 2 * (π / 2 - 1) / (π / 2 + 1) ≥ 2 - π / 2 := by
    rw [ge_iff_le, le_div_iff₀ hden]
    nlinarith [pi_gt_d2]
  linarith

end NLAlib

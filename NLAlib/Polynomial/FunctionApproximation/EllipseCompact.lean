import NLAlib.Polynomial.FunctionApproximation.EllipseGeometry

/-!
# Compact subsets of an open Bernstein ellipse

The focal-distance characterisation provides a smaller filled ellipse for every
compact subset. This is the domain exhaustion used in `bernstein-converse`.
-/

noncomputable section

open Set

namespace NLAlib

/-- Every compact subset of an open Bernstein ellipse lies in a smaller filled ellipse.
Source: Trefethen, ATAP, Thm 8.3; operator derivations §5,
helper for `bernstein-converse`. -/
theorem exists_lt_radius_subset_filledBernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ openBernsteinEllipse ρ) :
    ∃ r : ℝ, 1 < r ∧ r < ρ ∧ K ⊆ filledBernsteinEllipse r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨r, hr, hrρ⟩ := exists_between hρ
    exact ⟨r, hr, hrρ, empty_subset _⟩
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun z : ℂ => ‖z - 1‖ + ‖z + 1‖) K by fun_prop)
  have hzellipse := hsub hz
  rw [openBernsteinEllipse_eq_image_one_le_norm hρ] at hzellipse
  obtain ⟨w, hw, hwz⟩ := hzellipse
  obtain ⟨r, hwr, hrρ⟩ := exists_between hw.2
  have hr : 1 < r := hw.1.trans_lt hwr
  refine ⟨r, hr, hrρ, fun y hy => ?_⟩
  rw [mem_filledBernsteinEllipse_iff hr.le]
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith [hw.1])
  have hmax' : ‖y - 1‖ + ‖y + 1‖ ≤ ‖w‖ + ‖w‖⁻¹ := by
    rw [← norm_joukowski_sub_one_add_norm_joukowski_add_one hw0, hwz]
    exact hmax hy
  exact hmax'.trans (strictMonoOn_add_inv_Ici_one.monotoneOn hw.1 hr.le hwr.le)

end NLAlib

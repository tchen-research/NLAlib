import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Continuous barriers on a positive half-line

A continuous function which tends to zero cannot cross an excluded positive
level. A quadratic inequality provides the excluded level used for Dyson bounds.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace ContinuousOn

/-- A continuous function tending to zero stays below every positive level
that it never attains on the positive half-line. -/
theorem lt_of_tendsto_zero_of_ne {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) (hlim : Tendsto f atTop (𝓝 0))
    {C : ℝ} (hC : 0 < C) (hne : ∀ y : ℝ, 0 < y → f y ≠ C)
    {y : ℝ} (hy : 0 < y) : f y < C := by
  by_contra h
  have hlarge : C ≤ f y := le_of_not_gt h
  obtain ⟨Y, hY, hsmall⟩ :=
    ((eventually_ge_atTop y).and (hlim.eventually (gt_mem_nhds hC))).exists
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hY
    (hf.mono (fun t ht => lt_of_lt_of_le hy ht.1)) ⟨hsmall.le, hlarge⟩
  exact hne t (lt_of_lt_of_le hy ht.1) hft

/-- The small branch of a quadratic norm inequality is selected by
continuity and decay at infinity, with no branch-selection hypothesis. -/
theorem lt_two_div_of_quadratic {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) (hlim : Tendsto f atTop (𝓝 0))
    {δ q : ℝ} (hδ : 0 < δ) (hgap : 4 * q < δ ^ 2)
    (hquad : ∀ y : ℝ, 0 < y → δ * f y ≤ 1 + q * f y ^ 2)
    {y : ℝ} (hy : 0 < y) : f y < 2 / δ := by
  apply hf.lt_of_tendsto_zero_of_ne hlim (div_pos (by norm_num) hδ) _ hy
  intro t ht heq
  have h := hquad t ht
  rw [heq] at h
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hprod : δ * (2 / δ) = 2 := by field_simp
  rw [hprod] at h
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg δ)
  have hid : (1 + q * (2 / δ) ^ 2) * δ ^ 2 = δ ^ 2 + 4 * q := by
    field_simp
    ring
  rw [hid] at hmul
  nlinarith

end ContinuousOn

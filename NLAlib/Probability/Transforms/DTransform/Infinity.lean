import NLAlib.Probability.Transforms.DTransform.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The D-transform elasticity at infinity

The exact compact-support bounds squeeze the native derivative-based root
function to `-2`. Source: ScreeNOT, Lemma 8 and Supplement Appendix A.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace NLAlib

/-- The actual D-transform root function tends to `-2` at positive infinity.
Only compact support and the probability normalization are needed.
Source: ScreeNOT, Lemma 8.
atlas: scree-threshold-root (partial) -/
theorem tendsto_singularValuePsi_atTop (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hb : 0 ≤ b)
    (hsupport : μ.support ⊆ Icc 0 b) :
    Tendsto (singularValuePsi μ γ) atTop (𝓝 (-2)) := by
  have hgap : Tendsto (fun y : ℝ => y ^ 2 - b ^ 2) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(b ^ 2))
      (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hsmall : Tendsto (fun y : ℝ => 4 * b ^ 2 / (y ^ 2 - b ^ 2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := 4 * b ^ 2)).mul (tendsto_inv_atTop_zero.comp hgap)
  have hlower : Tendsto (fun y : ℝ => -2 - 4 * b ^ 2 / (y ^ 2 - b ^ 2))
      atTop (𝓝 (-2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (-2 : ℝ))).sub hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop b] with y hy
    exact (singularValuePsi_bounds μ hγ hγ1 hb hsupport hy).1
  · filter_upwards [eventually_gt_atTop b] with y hy
    exact (singularValuePsi_bounds μ hγ hγ1 hb hsupport hy).2

end NLAlib

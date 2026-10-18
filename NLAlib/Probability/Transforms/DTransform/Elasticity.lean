import NLAlib.Probability.Transforms.DTransform.Derivatives
import NLAlib.Probability.Transforms.DTransform.Moments
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict monotonicity of singular-value transform elasticity

The derivative is bounded below using the actual three-moment
Cauchy--Schwarz inequality. Source: ScreeNOT, Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

/-- The singular-value transform is positive above a nonnegative compact
probability-law support. -/
theorem singularValuePhi_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    0 < singularValuePhi μ y := by
  rw [singularValuePhi_eq_mul_moment]
  exact mul_pos (lt_of_le_of_lt hb hy) (dTransformMoment_pos μ hb hsupport hy 0)

/-- The actual logarithmic derivative of the singular-value transform is
expressed by its first two inverse-denominator moments. -/
theorem singularValueElasticity_eq_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValueElasticity μ y =
      1 - 2 * y ^ 2 * dTransformMoment μ 1 y / dTransformMoment μ 0 y := by
  unfold singularValueElasticity
  rw [(hasDerivAt_singularValuePhi μ hb hsupport hy).deriv, singularValuePhi_eq_mul_moment]
  field_simp [(dTransformMoment_pos μ hb hsupport hy 0).ne', (lt_of_le_of_lt hb hy).ne']

/-- Differentiating the actual logarithmic derivative involves only three
inverse-denominator moments. -/
theorem hasDerivAt_singularValueElasticity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    HasDerivAt (singularValueElasticity μ)
      (4 * y * (2 * y ^ 2 * dTransformMoment μ 2 y * dTransformMoment μ 0 y -
        y ^ 2 * dTransformMoment μ 1 y ^ 2 -
        dTransformMoment μ 1 y * dTransformMoment μ 0 y) / dTransformMoment μ 0 y ^ 2) y := by
  have h0 := hasDerivAt_dTransformMoment μ hb hsupport hy 0
  have h1 := hasDerivAt_dTransformMoment μ hb hsupport hy 1
  have hnum := (((hasDerivAt_id y).pow 2).const_mul 2).mul h1
  have hquot := (hnum.div h0 (dTransformMoment_pos μ hb hsupport hy 0).ne').const_sub 1
  have heq : singularValueElasticity μ =ᶠ[𝓝 y]
      (fun t => 1 - 2 * t ^ 2 * dTransformMoment μ 1 t / dTransformMoment μ 0 t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact singularValueElasticity_eq_moments μ hb hsupport ht
  convert! hquot.congr_of_eventuallyEq heq using 1
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_zero, Nat.cast_one,
    zero_add, mul_one, Nat.reduceAdd, Nat.cast_ofNat]
  field_simp [(dTransformMoment_pos μ hb hsupport hy 0).ne']
  ring

/-- A positive upper support point makes the actual elasticity derivative
strictly positive throughout the interval above the support. -/
theorem deriv_singularValueElasticity_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b)
    (hbmem : b ∈ μ.support) (hy : b < y) :
    0 < deriv (singularValueElasticity μ) y := by
  rw [(hasDerivAt_singularValueElasticity μ hb.le hsupport hy).deriv]
  have h0 := dTransformMoment_pos μ hb.le hsupport hy 0
  have h1 := dTransformMoment_pos μ hb.le hsupport hy 1
  have hcs := dTransformMoment_one_sq_le_zero_mul_two μ hb.le hsupport hy
  have hdef := sq_mul_dTransformMoment_one_sub_zero_pos μ hb hsupport hbmem hy
  have hcs' := mul_le_mul_of_nonneg_left hcs (sq_nonneg y)
  have hprod := mul_pos h1 hdef
  have hn : 0 < 2 * y ^ 2 * dTransformMoment μ 2 y * dTransformMoment μ 0 y -
      y ^ 2 * dTransformMoment μ 1 y ^ 2 -
      dTransformMoment μ 1 y * dTransformMoment μ 0 y := by nlinarith only [hcs', hprod]
  exact div_pos (mul_pos (mul_pos (by norm_num) (hb.trans hy)) hn) (sq_pos_of_pos h0)

/-- The actual logarithmic elasticity is strictly increasing above every
positive compact-support upper edge. -/
theorem strictMonoOn_singularValueElasticity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support) :
    StrictMonoOn (singularValueElasticity μ) (Ioi b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi b)
  · intro y hy
    exact (hasDerivAt_singularValueElasticity μ hb.le hsupport hy).continuousAt.continuousWithinAt
  · intro y hy
    exact deriv_singularValueElasticity_pos μ hb hsupport hbmem (interior_subset hy)

end NLAlib

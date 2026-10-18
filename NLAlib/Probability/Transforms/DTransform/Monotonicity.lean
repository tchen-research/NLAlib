import NLAlib.Probability.Transforms.DTransform.Elasticity
import NLAlib.Probability.Transforms.DTransform.Companion

/-!
# Monotonicity of the native D-transform root function

The product logarithmic derivative is the sum of the elasticities of two
actual compact-support probability laws. Source: ScreeNOT, Lemma 8 and
Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

/-- The companion transform is strictly positive above the common support. -/
theorem singularValueCompanionPhi_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b y : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    0 < singularValueCompanionPhi μ γ y := by
  let : IsProbabilityMeasure (dTransformCompanionMeasure μ γ) :=
    isProbabilityMeasure_dTransformCompanionMeasure μ hγ hγ1
  rw [← singularValuePhi_dTransformCompanionMeasure μ hγ hγ1 hb hsupport hy]
  exact singularValuePhi_pos _ hb (support_dTransformCompanionMeasure_subset μ hb hsupport) hy

/-- The actual derivative-based D-transform root function equals the sum of
the two actual logarithmic elasticities. -/
theorem singularValuePsi_eq_add_elasticity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b y : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValuePsi μ γ y = singularValueElasticity μ y +
      singularValueElasticity (dTransformCompanionMeasure μ γ) y := by
  let ν := dTransformCompanionMeasure μ γ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_dTransformCompanionMeasure μ hγ hγ1
  change singularValuePsi μ γ y = singularValueElasticity μ y + singularValueElasticity ν y
  have hsν : ν.support ⊆ Icc 0 b := support_dTransformCompanionMeasure_subset μ hb hsupport
  have heq : singularValueCompanionPhi μ γ =ᶠ[𝓝 y] singularValuePhi ν := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (singularValuePhi_dTransformCompanionMeasure μ hγ hγ1 hb hsupport ht).symm
  have hφ := (hasDerivAt_singularValuePhi μ hb hsupport hy).differentiableAt.hasDerivAt
  have hν := (hasDerivAt_singularValuePhi ν hb hsν hy).differentiableAt.hasDerivAt
  have hc := hν.congr_of_eventuallyEq heq
  have hD : HasDerivAt (singularValueDTransform μ γ)
      (deriv (singularValuePhi μ) y * singularValueCompanionPhi μ γ y +
        singularValuePhi μ y * deriv (singularValuePhi ν) y) y := by
    convert! hφ.mul hc using 1
  unfold singularValuePsi
  rw [hD.deriv]
  unfold singularValueDTransform singularValueElasticity
  rw [heq.eq_of_nhds]
  field_simp [(singularValuePhi_pos μ hb hsupport hy).ne',
    (singularValuePhi_pos ν hb hsν hy).ne']

/-- The actual D-transform root function is continuous above the compact
nonnegative support. Source: ScreeNOT, Lemma 8(1).
atlas: scree-threshold-root (partial) -/
theorem continuousOn_singularValuePsi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) :
    ContinuousOn (singularValuePsi μ γ) (Ioi b) := by
  let ν := dTransformCompanionMeasure μ γ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_dTransformCompanionMeasure μ hγ hγ1
  have hsν : ν.support ⊆ Icc 0 b := support_dTransformCompanionMeasure_subset μ hb hsupport
  have hc : ContinuousOn (fun y => singularValueElasticity μ y + singularValueElasticity ν y) (Ioi b) := by
    intro y hy
    exact ((hasDerivAt_singularValueElasticity μ hb hsupport hy).continuousAt.add
      (hasDerivAt_singularValueElasticity ν hb hsν hy).continuousAt).continuousWithinAt
  apply hc.congr
  intro y hy
  exact singularValuePsi_eq_add_elasticity μ hγ hγ1 hb hsupport hy

/-- The native D-transform logarithmic derivative is strictly increasing
above a positive upper support edge. Source: ScreeNOT, Lemma 8(1).
atlas: scree-threshold-root (partial) -/
theorem strictMonoOn_singularValuePsi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support) :
    StrictMonoOn (singularValuePsi μ γ) (Ioi b) := by
  let ν := dTransformCompanionMeasure μ γ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_dTransformCompanionMeasure μ hγ.le hγ1
  have hsν : ν.support ⊆ Icc 0 b := support_dTransformCompanionMeasure_subset μ hb.le hsupport
  have hbν : b ∈ ν.support := mem_support_dTransformCompanionMeasure μ hγ hbmem
  have hm := strictMonoOn_singularValueElasticity μ hb hsupport hbmem
  have hn := strictMonoOn_singularValueElasticity ν hb hsν hbν
  intro x hx y hy hxy
  rw [singularValuePsi_eq_add_elasticity μ hγ.le hγ1 hb.le hsupport hx,
    singularValuePsi_eq_add_elasticity μ hγ.le hγ1 hb.le hsupport hy]
  exact add_lt_add (hm hx hy hxy) (hn hx hy hxy)

end NLAlib

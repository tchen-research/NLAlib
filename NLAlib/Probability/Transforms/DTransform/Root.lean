import NLAlib.Probability.Transforms.DTransform.Edge
import NLAlib.ForMathlib.Analysis.Bisection
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual ScreeNOT threshold and certified midpoint bisection

The threshold is defined from the native probability-law D-transform, rather
than from a supplied crossing. Compact support, a nonzero support edge, and
edge thickness prove existence and uniqueness. Source: ScreeNOT, Lemma 8 and
Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

/-- The ScreeNOT threshold, defined by the actual `-4` crossing set. On the
regular compact-support laws considered below it is the unique crossing. -/
def screeThreshold (μ : Measure ℝ) (γ b : ℝ) : ℝ :=
  sInf {y | b < y ∧ -4 ≤ singularValuePsi μ γ y}

/-- The actual D-transform equation has exactly one solution above its edge,
and that solution lies in the universal bracket.
Source: ScreeNOT, Lemma 8.
atlas: scree-threshold-root (partial) -/
theorem existsUnique_singularValuePsi_eq_neg_four
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {γ b : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support)
    (hthick : Tendsto (singularValueEdgeMoment μ) (𝓝[>] b) atTop) :
    ∃! y, b < y ∧ y ≤ Real.sqrt 3 * b ∧ singularValuePsi μ γ y = -4 := by
  have hsqrt : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hhi : b < Real.sqrt 3 * b := by nlinarith [mul_lt_mul_of_pos_right hsqrt hb]
  have he := tendsto_singularValuePsi_atBot_of_edge_thickness μ hγ.le hγ1 hb hsupport hthick
  let : NeBot (𝓝[>] b) := nhdsWithin_Ioi_neBot le_rfl
  have hay : ∀ᶠ y in 𝓝[>] b, b < y := self_mem_nhdsWithin
  obtain ⟨a, ⟨ha, hpa⟩, hahi⟩ := ((hay.and (he.eventually_lt_atBot (-4))).and
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hhi))).exists
  have hc := (continuousOn_singularValuePsi μ hγ.le hγ1 hb.le hsupport).mono
    (show Icc a (Real.sqrt 3 * b) ⊆ Ioi b from fun x hx => ha.trans_le hx.1)
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc hahi.le hc
    (show (-4 : ℝ) ∈ Icc (singularValuePsi μ γ a)
      (singularValuePsi μ γ (Real.sqrt 3 * b)) from
      ⟨hpa.le, neg_four_le_singularValuePsi_sqrt_three_mul μ hγ.le hγ1 hb hsupport⟩)
  refine ⟨r, ⟨ha.trans_le hr.1, hr.2, hre⟩, ?_⟩
  intro y hy
  exact (strictMonoOn_singularValuePsi μ hγ hγ1 hb hsupport hbmem).injOn
    hy.1 (ha.trans_le hr.1) (hy.2.2.trans hre.symm)

/-- A genuine crossing identifies the infimum definition of the threshold. -/
theorem screeThreshold_eq_of_root (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b r : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support)
    (hr : b < r) (hre : singularValuePsi μ γ r = -4) :
    screeThreshold μ γ b = r := by
  have hmem : r ∈ {y | b < y ∧ -4 ≤ singularValuePsi μ γ y} := ⟨hr, hre.symm.le⟩
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨r, hmem⟩
  · intro y hy
    by_contra h
    have hlt := strictMonoOn_singularValuePsi μ hγ hγ1 hb hsupport hbmem hy.1 hr
      (lt_of_not_ge h)
    rw [hre] at hlt
    exact (not_lt_of_ge hy.2) hlt
  · intro w hw
    exact ⟨r, hmem, hw⟩

/-- The defined threshold satisfies the native equation and universal bracket.
Source: ScreeNOT, Lemma 8.
atlas: scree-threshold-root (partial) -/
theorem screeThreshold_spec (μ : Measure ℝ) [IsProbabilityMeasure μ] {γ b : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support)
    (hthick : Tendsto (singularValueEdgeMoment μ) (𝓝[>] b) atTop) :
    b < screeThreshold μ γ b ∧ screeThreshold μ γ b ≤ Real.sqrt 3 * b ∧
      singularValuePsi μ γ (screeThreshold μ γ b) = -4 := by
  obtain ⟨r, hr, _⟩ := existsUnique_singularValuePsi_eq_neg_four μ hγ hγ1 hb hsupport hbmem hthick
  rwa [screeThreshold_eq_of_root μ hγ hγ1 hb hsupport hbmem hr.1 hr.2.2]

/-- Above the support edge, the threshold equation holds precisely at the
defined threshold. This also excludes any further crossing beyond the upper
bracket. Source: ScreeNOT, Lemma 8.
atlas: scree-threshold-root (partial) -/
theorem singularValuePsi_eq_neg_four_iff_eq_screeThreshold
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {γ b y : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support)
    (hthick : Tendsto (singularValueEdgeMoment μ) (𝓝[>] b) atTop) (hy : b < y) :
    singularValuePsi μ γ y = -4 ↔ y = screeThreshold μ γ b := by
  constructor
  · intro he
    exact (screeThreshold_eq_of_root μ hγ hγ1 hb hsupport hbmem hy he).symm
  · rintro rfl
    exact (screeThreshold_spec μ hγ hγ1 hb hsupport hbmem hthick).2.2

/-- Midpoint bisection of the actual threshold equation retains the threshold
and has the exact width `(sqrt 3 - 1) * b / 2^j`. The singular edge is never
evaluated. Source: ScreeNOT, Supplement Appendix A.
atlas: scree-threshold-root (partial) -/
theorem bisectionInterval_screeThreshold (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support)
    (hthick : Tendsto (singularValueEdgeMoment μ) (𝓝[>] b) atTop) (j : ℕ) :
    let p := bisectionInterval (singularValuePsi μ γ) (-4) b (Real.sqrt 3 * b) j
    b ≤ p.1 ∧ p.1 < screeThreshold μ γ b ∧ screeThreshold μ γ b ≤ p.2 ∧
      p.2 - p.1 = (Real.sqrt 3 - 1) * b / 2 ^ j := by
  obtain ⟨hl, hu, he⟩ := screeThreshold_spec μ hγ hγ1 hb hsupport hbmem hthick
  have hp := bisectionInterval_contains_root
    (strictMonoOn_singularValuePsi μ hγ hγ1 hb hsupport hbmem) he le_rfl hl hu j
  refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
  rw [bisectionInterval_sub]
  ring

end NLAlib

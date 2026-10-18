import NLAlib.Probability.Transforms.DTransform.Root
import NLAlib.Probability.Transforms.DTransform.WeakContinuity

/-! # Stability of the actual ScreeNOT threshold

Weak convergence and convergence of the support edge give convergence of the
native D-transform equation at every fixed point above the limiting edge.
Strict monotonicity then traps the actual thresholds between any two nearby
test points. Source: ScreeNOT, Lemma 3 and Supplement Appendix D.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

/-- The actual ScreeNOT thresholds converge under weak convergence of the
probability laws together with convergence of their actual positive support
edges and aspect ratios. All roots and transform continuity are derived from
the native law hypotheses. Source: ScreeNOT, Lemma 3 and Supplement Appendix
D.1.
atlas: scree-threshold-root (partial) -/
theorem tendsto_screeThreshold_of_weak_convergence
    {I : Type*} {l : Filter I} {μs : I → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l (𝓝 μ)) {bs γs : I → ℝ} {b γ : ℝ}
    (hbs : Tendsto bs l (𝓝 b)) (hγs : Tendsto γs l (𝓝 γ))
    (hbs0 : ∀ i, 0 < bs i) (hb : 0 < b)
    (hγs0 : ∀ i, 0 < γs i) (hγs1 : ∀ i, γs i ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hs : ∀ i, (μs i : Measure ℝ).support ⊆ Icc 0 (bs i))
    (hμ : (μ : Measure ℝ).support ⊆ Icc 0 b)
    (hsmem : ∀ i, bs i ∈ (μs i : Measure ℝ).support) (hbmem : b ∈ (μ : Measure ℝ).support)
    (hsthick : ∀ i, Tendsto (singularValueEdgeMoment (μs i : Measure ℝ)) (𝓝[>] (bs i)) atTop)
    (hthick : Tendsto (singularValueEdgeMoment (μ : Measure ℝ)) (𝓝[>] b) atTop) :
    Tendsto (fun i => screeThreshold (μs i : Measure ℝ) (γs i) (bs i)) l
      (𝓝 (screeThreshold (μ : Measure ℝ) γ b)) := by
  have hT := screeThreshold_spec (μ : Measure ℝ) hγ hγ1 hb hμ hbmem hthick
  have hTs i := screeThreshold_spec (μs i : Measure ℝ) (hγs0 i) (hγs1 i)
    (hbs0 i) (hs i) (hsmem i) (hsthick i)
  have hf := strictMonoOn_singularValuePsi (μ : Measure ℝ) hγ hγ1 hb hμ hbmem
  have hfs i := strictMonoOn_singularValuePsi (μs i : Measure ℝ) (hγs0 i) (hγs1 i)
    (hbs0 i) (hs i) (hsmem i)
  have hconv (x : ℝ) (hx : b < x) := tendsto_singularValuePsi_of_weak_convergence
    hweak hbs hγs (fun i => (hbs0 i).le) hb.le hγ.le hγ1 hs hμ hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨x, hax, hxT⟩ := exists_between (max_lt_iff.mpr ⟨ha, hT.1⟩)
    have hbx : b < x := (le_max_right a b).trans_lt hax
    have hax' : a < x := (le_max_left a b).trans_lt hax
    have hpx : singularValuePsi (μ : Measure ℝ) γ x < -4 := by
      rw [← hT.2.2]
      exact hf hbx hT.1 hxT
    filter_upwards [(hconv x hbx).eventually (Iio_mem_nhds hpx),
      hbs.eventually (Iio_mem_nhds hbx)] with i hi hbi
    have hxt : x < screeThreshold (μs i : Measure ℝ) (γs i) (bs i) := by
      apply ((hfs i).lt_iff_lt hbi (hTs i).1).mp
      rwa [(hTs i).2.2]
    exact hax'.trans hxt
  · intro a ha
    obtain ⟨x, hTx, hxa⟩ := exists_between ha
    have hbx : b < x := hT.1.trans hTx
    have hpx : -4 < singularValuePsi (μ : Measure ℝ) γ x := by
      rw [← hT.2.2]
      exact hf hT.1 hbx hTx
    filter_upwards [(hconv x hbx).eventually (Ioi_mem_nhds hpx),
      hbs.eventually (Iio_mem_nhds hbx)] with i hi hbi
    have htx : screeThreshold (μs i : Measure ℝ) (γs i) (bs i) < x := by
      apply ((hfs i).lt_iff_lt (hTs i).1 hbi).mp
      rwa [(hTs i).2.2]
    exact htx.trans hxa

end NLAlib

import NLAlib.Probability.Transforms.DTransform.Formula
import NLAlib.ForMathlib.MeasureTheory.CompactSupportWeakConvergence

/-! # Weak-law continuity of singular-value D-transforms above the support

The tests are continuous on a common compact interval lying strictly below
the evaluation point. Convergence of the actual support bounds supplies that
interval eventually. Source: ScreeNOT, Lemma 3 and Supplement Appendix D.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace NLAlib

/-- Weak convergence together with convergence of support bounds gives
convergence of each actual inverse-denominator moment above the limit edge. -/
theorem tendsto_dTransformMoment_of_weak_convergence
    {I : Type*} {l : Filter I} {μs : I → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l (𝓝 μ)) {bs : I → ℝ} {b y : ℝ}
    (hbs : Tendsto bs l (𝓝 b)) (hb : 0 ≤ b)
    (hs : ∀ i, (μs i : Measure ℝ).support ⊆ Icc 0 (bs i))
    (hμ : (μ : Measure ℝ).support ⊆ Icc 0 b) (hy : b < y) (k : ℕ) :
    Tendsto (fun i => dTransformMoment (μs i : Measure ℝ) k y) l
      (𝓝 (dTransformMoment (μ : Measure ℝ) k y)) := by
  let c := (b + y) / 2
  have hbc : b < c := by dsimp [c]; linarith
  have hcy : c < y := by dsimp [c]; linarith
  have hc : 0 ≤ c := hb.trans hbc.le
  have hsc : ∀ᶠ i in l, (μs i : Measure ℝ).support ⊆ Icc 0 c := by
    filter_upwards [hbs.eventually (Iio_mem_nhds hbc)] with i hi z hz
    exact ⟨(hs i hz).1, (hs i hz).2.trans hi.le⟩
  have hμc : (μ : Measure ℝ).support ⊆ Icc 0 c :=
    fun z hz => ⟨(hμ hz).1, (hμ hz).2.trans hbc.le⟩
  exact ProbabilityMeasure.tendsto_integral_of_support_subset_Icc hweak hc hsc hμc
    (((continuousOn_const.sub (continuousOn_id.pow 2)).inv₀
      (fun z hz => (dTransform_denominator_pos hc hcy hz).ne')).pow (k + 1))

/-- The actual derivative-defined D-transform root function is continuous
under weak convergence and convergence of the upper support edge, at every
fixed point strictly above the limiting edge. No derivative-convergence
assumption is supplied. Source: ScreeNOT, Lemma 3, Supplement Appendix D.1. -/
theorem tendsto_singularValuePsi_of_weak_convergence
    {I : Type*} {l : Filter I} {μs : I → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l (𝓝 μ)) {bs γs : I → ℝ} {b γ y : ℝ}
    (hbs : Tendsto bs l (𝓝 b)) (hγs : Tendsto γs l (𝓝 γ))
    (hbs0 : ∀ i, 0 ≤ bs i) (hb : 0 ≤ b) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hs : ∀ i, (μs i : Measure ℝ).support ⊆ Icc 0 (bs i))
    (hμ : (μ : Measure ℝ).support ⊆ Icc 0 b) (hy : b < y) :
    Tendsto (fun i => singularValuePsi (μs i : Measure ℝ) (γs i) y) l
      (𝓝 (singularValuePsi (μ : Measure ℝ) γ y)) := by
  have h0 := tendsto_dTransformMoment_of_weak_convergence hweak hbs hb hs hμ hy 0
  have h1 := tendsto_dTransformMoment_of_weak_convergence hweak hbs hb hs hμ hy 1
  have hy0 : y ≠ 0 := (hb.trans_lt hy).ne'
  have hp : Tendsto (fun i => singularValuePhi (μs i : Measure ℝ) y) l
      (𝓝 (singularValuePhi (μ : Measure ℝ) y)) := by
    simpa only [singularValuePhi_eq_mul_moment] using (tendsto_const_nhds (x := y)).mul h0
  have hd := h0.sub ((tendsto_const_nhds (x := 2 * y ^ 2)).mul h1)
  have hc : Tendsto (fun i => singularValueCompanionPhi (μs i : Measure ℝ) (γs i) y) l
      (𝓝 (singularValueCompanionPhi (μ : Measure ℝ) γ y)) := by
    exact (hγs.mul hp).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hγs).div
      tendsto_const_nhds hy0)
  have hdc := (hγs.mul hd).sub
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hγs).div tendsto_const_nhds (pow_ne_zero 2 hy0))
  have hden : singularValuePhi (μ : Measure ℝ) y *
      singularValueCompanionPhi (μ : Measure ℝ) γ y ≠ 0 :=
    mul_ne_zero (singularValuePhi_pos (μ : Measure ℝ) hb hμ hy).ne'
      (singularValueCompanionPhi_pos (μ : Measure ℝ) hγ hγ1 hb hμ hy).ne'
  have ht := ((tendsto_const_nhds (x := y)).mul ((hd.mul hc).add (hp.mul hdc))).div
    (hp.mul hc) hden
  rw [← singularValuePsi_eq_moments (μ : Measure ℝ) hb hμ hy] at ht
  apply ht.congr'
  filter_upwards [hbs.eventually (Iio_mem_nhds hy)] with i hi
  exact (singularValuePsi_eq_moments (μs i : Measure ℝ) (hbs0 i) (hs i) hi).symm

end NLAlib

import Mathlib.Analysis.Convex.Integral
import Mathlib.Topology.Sequences

/-!
# Jensen inequality on a nonclosed convex domain

Lean name: `NLAlib.ch3_lieb_jensen`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Jensen inequality (2.2.2), printed p. 25, and its use in Corollary 3.4.2, printed p. 35. Auxiliary Banach-space formulation with explicit integrability, continuity, and mean-membership hypotheses.
-/
open MeasureTheory
set_option autoImplicit false
open Set Filter
open scoped Topology

/-- Jensen's inequality on a possibly nonclosed convex domain, provided the mean belongs to it. -/
theorem NLAlib.ch3_lieb_jensen {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set E) (g : E → ℝ) (f : Ω → E)
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ)
    (hgf : Integrable (fun ω => g (f ω)) μ) (hm : (∫ ω, f ω ∂μ) ∈ s) :
    (∫ ω, g (f ω) ∂μ) ≤ g (∫ ω, f ω ∂μ)  := by
  let S : Set (E × ℝ) := {p | p.1 ∈ s ∧ p.2 ≤ g p.1}
  have hi : (∫ ω, (f ω, g (f ω)) ∂μ) ∈ closure S :=
    hg.convex_hypograph.closure.integral_mem isClosed_closure
      (hfs.mono fun ω hω => subset_closure ⟨hω, le_rfl⟩) (hf.prodMk hgf)
  rw [integral_pair hf hgf] at hi
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hi
  have hglim : Tendsto (fun n => g (u n).1) atTop (𝓝 (g (∫ ω, f ω ∂μ))) :=
    (hgc _ hm).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_fst.tendsto _).comp hlim, Eventually.of_forall fun n => (hu n).1⟩)
  exact le_of_tendsto_of_tendsto' ((continuous_snd.tendsto _).comp hlim) hglim (fun n => (hu n).2)


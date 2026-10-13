import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality on a non-closed convex set

`ConcaveOn.le_map_integral_of_integral_mem`: `∫ g ∘ f ≤ g (∫ f)` for `g` concave and continuous on
a convex set `s` that need not be closed, provided the mean of `f` lies in `s` (Mathlib's
`ConcaveOn.le_map_integral` needs `s` closed). Moved from
`NLAlib.Probability.Concentration.Matrix.LiebJensen` (dedup round, 2026-10-12).
-/

open MeasureTheory Set Filter
open scoped Topology

/-- Jensen's inequality `∫ g ∘ f ≤ g (∫ f)` for `g` concave and continuous on a possibly non-closed
convex set `s`, provided the mean of `f` lies in `s`.

Tropp 2015, eq. (2.2.2), as used in Corollary 3.4.2. Atlas: `matrix-laplace`. Ported from the
Prove2me mission *An Introduction to Matrix Concentration Inequalities, Ch 3*.

Variant of Mathlib's `ConcaveOn.le_map_integral`, which needs `s` closed. -/
theorem ConcaveOn.le_map_integral_of_integral_mem {Ω E : Type*} [MeasurableSpace Ω]
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

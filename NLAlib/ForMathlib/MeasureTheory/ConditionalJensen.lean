import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Topology.Sequences

/-!
# Conditional Jensen on a nonclosed convex domain

The conditional mean lies in the closure of the actual hypograph. Continuity at that
mean then gives conditional Jensen whenever mean membership in the domain is proved.
This keeps the probability space arbitrary and avoids boundary regularization.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NLAlib

/-- Conditional Jensen for a concave continuous function on a possibly nonclosed convex
domain, provided its actual conditional mean lies in that domain almost everywhere.
The closed hypograph argument proves the inequality without assuming conditional Jensen.
Source: Mathlib conditional Jensen and closed convex conditional-mean membership;
operator rederivations Section 3.2 (`eq:condlieb`), foundation for `matrix-freedman`. -/
theorem ConcaveOn.condExp_map_le_of_condExp_mem {Ω E : Type*}
    {m mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set E} {g : E → ℝ} {f : Ω → E} (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ)
    (hgf : Integrable (fun ω => g (f ω)) μ) (hmean : ∀ᵐ ω ∂μ, μ[f | m] ω ∈ s) :
    μ[(fun ω => g (f ω)) | m] ≤ᵐ[μ] fun ω => g (μ[f | m] ω) := by
  let S : Set (E × ℝ) := {p | p.1 ∈ s ∧ p.2 ≤ g p.1}
  let p : Ω → E × ℝ := fun ω => (f ω, g (f ω))
  have hp : Integrable p μ := hf.prodMk hgf
  have hmem : ∀ᵐ ω ∂μ, μ[p | m] ω ∈ closure S :=
    hg.convex_hypograph.closure.condExp_mem hm hp isClosed_closure
      (hfs.mono fun ω hω => subset_closure ⟨hω, le_rfl⟩)
  have hfst := (ContinuousLinearMap.fst ℝ E ℝ).comp_condExp_comm (m := m) hp
  have hsnd := (ContinuousLinearMap.snd ℝ E ℝ).comp_condExp_comm (m := m) hp
  filter_upwards [hmem, hfst, hsnd, hmean] with ω hω h₁ h₂ hmean
  change (μ[p | m] ω).1 = μ[f | m] ω at h₁
  change (μ[p | m] ω).2 = μ[(fun ω => g (f ω)) | m] ω at h₂
  have heq : μ[p | m] ω = (μ[f | m] ω, μ[(fun ω => g (f ω)) | m] ω) := Prod.ext h₁ h₂
  rw [heq] at hω
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hω
  have hglim : Tendsto (fun n => g (u n).1) atTop (𝓝 (g (μ[f | m] ω))) :=
    (hgc _ hmean).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_fst.tendsto _).comp hlim, Eventually.of_forall fun n => (hu n).1⟩)
  exact le_of_tendsto_of_tendsto' ((continuous_snd.tendsto _).comp hlim) hglim (fun n => (hu n).2)

end NLAlib

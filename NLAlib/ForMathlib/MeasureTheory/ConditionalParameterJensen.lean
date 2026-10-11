import NLAlib.ForMathlib.MeasureTheory.ConditionalJensen
import NLAlib.ForMathlib.MeasureTheory.ConditionalComparison
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Conditional Jensen with a measurable parameter

Countably many dense fixed parameters share a common null set. Comparison on measurable
parameter balls and the exact exponential perturbation factor pass to a predictable
parameter, with no regular conditional-probability kernel on the underlying space.
-/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace NLAlib

/-- Actual conditional Jensen with a conditioning-measurable parameter for a concave
continuous family whose parameter perturbations satisfy an exponential comparison.
Countable dense fixed parameters and actual conditional comparison on measurable cuts
prove this from scalar hypotheses, without assuming a conditional Jensen inequality.
Source: operator rederivations `eq:condlieb`, predictable-offset passage;
atlas `matrix-freedman` (partial). -/
theorem condExp_family_le_family_condExp_of_exponential_comparison
    {Ω E P : Type*} {m mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P] [Nonempty P]
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set E} {g : P → E → ℝ} {f : Ω → E} {U : Ω → P}
    (hconc : ∀ p, ConcaveOn ℝ s (g p)) (hcont : ∀ p, ContinuousOn (g p) s)
    (hcomp : ∀ p q, ∀ x ∈ s, ∀ δ : ℝ, 0 ≤ δ → dist p q ≤ δ → g p x ≤ Real.exp δ * g q x)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ)
    (hfixed : ∀ p, Integrable (fun ω => g p (f ω)) μ)
    (hactual : Integrable (fun ω => g (U ω) (f ω)) μ)
    (hmean : ∀ᵐ ω ∂μ, μ[f | m] ω ∈ s) (hU : Measurable[m] U) :
    μ[(fun ω => g (U ω) (f ω)) | m] ≤ᵐ[μ] fun ω => g (U ω) (μ[f | m] ω) := by
  let u : ℕ → P := denseSeq P
  let δ : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hδ : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hJ : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      μ[(fun ω => g (u j) (f ω)) | m] ω ≤ g (u j) (μ[f | m] ω) :=
    ae_all_iff.mpr fun j => ConcaveOn.condExp_map_le_of_condExp_mem hm
      (hconc (u j)) (hcont (u j)) hfs hf (hfixed (u j)) hmean
  have hcuts : ∀ᵐ ω ∂μ, ∀ e : ℕ × ℕ, dist (U ω) (u e.1) < δ e.2 →
      μ[(fun ω => g (U ω) (f ω)) | m] ω ≤
        Real.exp (δ e.2) * μ[(fun ω => g (u e.1) (f ω)) | m] ω := by
    apply ae_all_iff.mpr
    intro e
    let C : Set Ω := {ω | dist (U ω) (u e.1) < δ e.2}
    have hconst : Measurable[m] (fun _ : Ω => u e.1) := measurable_const
    have hδconst : Measurable[m] (fun _ : Ω => δ e.2) := measurable_const
    have hC : MeasurableSet[m] C := by
      let : MeasurableSpace Ω := m
      exact measurableSet_lt (hU.dist hconst) hδconst
    have hpoint : ∀ᵐ ω ∂μ, ω ∈ C → g (U ω) (f ω) ≤ Real.exp (δ e.2) * g (u e.1) (f ω) := by
      filter_upwards [hfs] with ω hω
      intro hωC
      exact hcomp _ _ _ hω _ (hδ e.2).le (le_of_lt hωC)
    have hc := ae_condExp_le_condExp_on_of_ae_le_on hm hactual
      ((hfixed (u e.1)).const_mul (Real.exp (δ e.2))) hC hpoint
    filter_upwards [hc, condExp_smul (Real.exp (δ e.2)) (fun ω => g (u e.1) (f ω)) m]
      with ω hω hscale
    intro hnear
    have hh := hω hnear
    have hs : μ[(fun ω => Real.exp (δ e.2) * g (u e.1) (f ω)) | m] ω =
        Real.exp (δ e.2) * μ[(fun ω => g (u e.1) (f ω)) | m] ω := by
      change μ[(fun ω => Real.exp (δ e.2) • g (u e.1) (f ω)) | m] ω =
        Real.exp (δ e.2) • μ[(fun ω => g (u e.1) (f ω)) | m] ω at hscale
      simpa only [smul_eq_mul] using hscale
    rw [hs] at hh
    exact hh
  filter_upwards [hJ, hcuts, hmean] with ω hJω hcutsω hmeanω
  have hbound : ∀ k : ℕ, μ[(fun ω => g (U ω) (f ω)) | m] ω ≤
      Real.exp (2 * δ k) * g (U ω) (μ[f | m] ω) := by
    intro k
    obtain ⟨j, hj⟩ := (denseRange_denseSeq P).exists_dist_lt (U ω) (hδ k)
    have hfirst := hcutsω (j, k) hj
    have hreverse := hcomp (u j) (U ω) _ hmeanω (δ k) (hδ k).le
      (by simpa only [dist_comm] using hj.le)
    calc μ[(fun ω => g (U ω) (f ω)) | m] ω ≤
          Real.exp (δ k) * μ[(fun ω => g (u j) (f ω)) | m] ω := hfirst
      _ ≤ Real.exp (δ k) * g (u j) (μ[f | m] ω) :=
        mul_le_mul_of_nonneg_left (hJω j) (Real.exp_pos _).le
      _ ≤ Real.exp (δ k) * (Real.exp (δ k) * g (U ω) (μ[f | m] ω)) :=
        mul_le_mul_of_nonneg_left hreverse (Real.exp_pos _).le
      _ = Real.exp (2 * δ k) * g (U ω) (μ[f | m] ω) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
  have hlim : Tendsto (fun k => Real.exp (2 * δ k) * g (U ω) (μ[f | m] ω)) atTop
      (𝓝 (g (U ω) (μ[f | m] ω))) := by
    have htwo : Tendsto (fun k => 2 * δ k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hδlim.const_mul 2
    simpa only [Function.comp_def, Real.exp_zero, one_mul] using
      ((Real.continuous_exp.tendsto (0 : ℝ)).comp htwo).mul_const (g (U ω) (μ[f | m] ω))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound

end NLAlib

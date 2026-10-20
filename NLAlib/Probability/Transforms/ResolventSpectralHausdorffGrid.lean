import NLAlib.Probability.Transforms.ResolventSpectralGrid
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Two-sided spectral distances from a shared resolvent grid

Both directed native spectral inclusions use one deterministic grid. A
single union bound counts each two-sided pointwise failure only once.
Source: arXiv:2201.05142v3, Proposition 7.7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Two-sided actual resolvent comparisons on a common finite covering
grid control the Hausdorff distance of the native spectra. The bound uses
outer probabilities and requires only almost-everywhere Hermitian support.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_hausdorffDist_spectra_gt_le_resolvent_grid
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Ω → Matrix n n ℂ)
    (hA : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (hB : ∀ᵐ ω ∂μ, (B ω).IsHermitian)
    (N : Finset ℝ) {η C δ ε : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (herror : δ+(C+1)*ε/η^2 ≤ (2*η)⁻¹) :
    μ.real {ω | 2*C*η < Metric.hausdorffDist (spectrum ℝ (A ω)) (spectrum ℝ (B ω))} ≤
      μ.real {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε} +
      μ.real {ω | ¬ ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ N, |ξ-u| ≤ ε} +
      ∑ u ∈ N, μ.real {ω |
        C*specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
          specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I)) ∨
        C*specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
          specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))} := by
  classical
  let F : Set Ω := {ω | 2*C*η <
    Metric.hausdorffDist (spectrum ℝ (A ω)) (spectrum ℝ (B ω))}
  let L : Set Ω := {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε}
  let K : Set Ω := {ω | ¬ ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ N, |ξ-u| ≤ ε}
  let E (u : ℝ) : Set Ω := {ω |
    C*specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
      specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I)) ∨
    C*specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
      specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))}
  have hsub : ∀ᵐ ω ∂μ, ω ∈ F → ω ∈ (L ∪ K) ∪ ⋃ u ∈ N, E u := by
    filter_upwards [hA, hB] with ω hωA hωB
    intro hf
    by_cases hcoverA : ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε
    · by_cases hcoverB : ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ N, |ξ-u| ≤ ε
      · by_cases hbad : ∃ u ∈ N, ω ∈ E u
        · obtain ⟨u, hu, he⟩ := hbad
          exact Or.inr (Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu he))
        · have hpoint (u : ℝ) (hu : u ∈ N) : ω ∉ E u := fun hh => hbad ⟨u,hu,hh⟩
          have hforward := forall_exists_mem_spectrum_dist_le_of_resolvent_net
            hωA hωB (N : Set ℝ) hη hC hcoverA (fun u hu =>
              le_of_not_gt (fun hh => hpoint u hu (Or.inl hh))) herror
          have hreverse := forall_exists_mem_spectrum_dist_le_of_resolvent_net
            hωB hωA (N : Set ℝ) hη hC hcoverB (fun u hu =>
              le_of_not_gt (fun hh => hpoint u hu (Or.inr hh))) herror
          exact False.elim (not_lt_of_ge (Metric.hausdorffDist_le_of_mem_dist
            (mul_nonneg (mul_nonneg (by norm_num) hC) hη.le) hforward hreverse) hf)
      · exact Or.inl (Or.inr hcoverB)
    · exact Or.inl (Or.inl hcoverA)
  have hm : μ.real F ≤ μ.real ((L ∪ K) ∪ ⋃ u ∈ N, E u) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  exact hm.trans ((measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _)
      (measureReal_biUnion_finset_le N E)))

end NLAlib

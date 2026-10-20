import NLAlib.Matrix.Spectral.ResolventSpectralNet
import Mathlib.MeasureTheory.Measure.Real

/-!
# Spectral inclusion probabilities from actual resolvents on finite grids

The deterministic parameter estimate and finite union bound reduce the
failure probability of native spectral inclusion to spectral localization
and the actual resolvent comparisons on the grid.
Source: arXiv:2201.05142v3, Propositions 7.4 and 7.7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- A deterministic finite grid bounds the probability that the actual
source spectrum is not within `2*C*η` of the actual comparison spectrum.
Almost-everywhere Hermitian support suffices; no eigenvalue selections or
spectral measurability assumptions are required for this outer-measure bound.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_spectral_inclusion_failure_le_resolvent_grid
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Ω → Matrix n n ℂ)
    (hA : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (hB : ∀ᵐ ω ∂μ, (B ω).IsHermitian)
    (N : Finset ℝ) {η C δ ε : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (herror : δ+(C+1)*ε/η^2 ≤ (2*η)⁻¹) :
    μ.real {ω | ∃ ξ ∈ spectrum ℝ (A ω),
      ∀ β ∈ spectrum ℝ (B ω), 2*C*η < dist ξ β} ≤
        μ.real {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε} +
          ∑ u ∈ N, μ.real {ω |
            C*specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
              specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I))} := by
  classical
  let F : Set Ω := {ω | ∃ ξ ∈ spectrum ℝ (A ω),
    ∀ β ∈ spectrum ℝ (B ω), 2*C*η < dist ξ β}
  let L : Set Ω := {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε}
  let E (u : ℝ) : Set Ω := {ω |
    C*specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ <
      specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I))}
  have hs : ∀ᵐ ω ∂μ, ω ∈ F → ω ∈ L ∪ ⋃ u ∈ N, E u := by
    filter_upwards [hA, hB] with ω hωA hωB
    intro hf
    by_cases hcover : ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε
    · right
      have hn : ¬ ∀ u ∈ N,
          specNorm (resolvent (A ω) ((u : ℂ)+(η : ℂ)*Complex.I)) ≤
            C*specNorm (resolvent (B ω) ((u : ℂ)+(η : ℂ)*Complex.I))+δ := by
        intro hcmp
        obtain ⟨ξ, hξ, hfar⟩ := hf
        obtain ⟨β, hβ, hclose⟩ := forall_exists_mem_spectrum_dist_le_of_resolvent_net
          hωA hωB (N : Set ℝ) hη hC hcover hcmp herror ξ hξ
        exact not_lt_of_ge hclose (hfar β hβ)
      push Not at hn
      obtain ⟨u, hu, hbad⟩ := hn
      exact Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu hbad)
    · exact Or.inl hcover
  have hm : μ.real F ≤ μ.real (L ∪ ⋃ u ∈ N, E u) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hs)
  exact hm.trans ((measureReal_union_le _ _).trans
    (add_le_add le_rfl (measureReal_biUnion_finset_le N E)))

end NLAlib

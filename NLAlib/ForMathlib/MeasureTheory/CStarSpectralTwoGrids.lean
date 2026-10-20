import NLAlib.ForMathlib.Analysis.CStarAlgebra.ResolventSpectralNet
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Two resolvent grids control actual spectral Hausdorff distance -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace MeasureTheory

/-- Two actual finite resolvent grids, one for each spectrum, give a
probability bound for their Hausdorff distance. The target algebras may differ
and their spectra may be infinite. Finite measures and outer events suffice. -/
theorem measureReal_hausdorffDist_spectra_gt_le_two_resolvent_grids
    {Ω E F : Type*} [MeasurableSpace Ω] [CStarAlgebra E] [CStarAlgebra F]
    [Nontrivial E] [Nontrivial F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → E) (B : Ω → F)
    (hA : ∀ᵐ ω ∂μ, IsSelfAdjoint (A ω)) (hB : ∀ᵐ ω ∂μ, IsSelfAdjoint (B ω))
    (N M : Finset ℝ) {η C δ ε : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (herror : δ + (C + 1) * ε / η^2 ≤ (2 * η)⁻¹) :
    μ.real {ω | 2 * C * η < Metric.hausdorffDist (spectrum ℝ (A ω)) (spectrum ℝ (B ω))} ≤
      μ.real {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε} +
      μ.real {ω | ¬ ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ M, |ξ-u| ≤ ε} +
      (∑ u ∈ N, μ.real {ω |
        C * ‖resolvent (B ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖ + δ <
          ‖resolvent (A ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖}) +
      ∑ u ∈ M, μ.real {ω |
        C * ‖resolvent (A ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖ + δ <
          ‖resolvent (B ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖} := by
  classical
  let Bad : Set Ω := {ω | 2 * C * η <
    Metric.hausdorffDist (spectrum ℝ (A ω)) (spectrum ℝ (B ω))}
  let LA : Set Ω := {ω | ¬ ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε}
  let LB : Set Ω := {ω | ¬ ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ M, |ξ-u| ≤ ε}
  let EF (u : ℝ) : Set Ω := {ω |
    C * ‖resolvent (B ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖ + δ <
      ‖resolvent (A ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖}
  let ER (u : ℝ) : Set Ω := {ω |
    C * ‖resolvent (A ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖ + δ <
      ‖resolvent (B ω) ((u : ℂ) + (η : ℂ) * Complex.I)‖}
  have hsub : ∀ᵐ ω ∂μ, ω ∈ Bad → ω ∈ ((LA ∪ LB) ∪ ⋃ u ∈ N, EF u) ∪ ⋃ u ∈ M, ER u := by
    filter_upwards [hA, hB] with ω hωA hωB
    intro hf
    by_cases hcoverA : ∀ ξ ∈ spectrum ℝ (A ω), ∃ u ∈ N, |ξ-u| ≤ ε
    · by_cases hcoverB : ∀ ξ ∈ spectrum ℝ (B ω), ∃ u ∈ M, |ξ-u| ≤ ε
      · by_cases hbadF : ∃ u ∈ N, ω ∈ EF u
        · obtain ⟨u, hu, he⟩ := hbadF
          exact Or.inl (Or.inr (Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu he)))
        · by_cases hbadR : ∃ u ∈ M, ω ∈ ER u
          · obtain ⟨u, hu, he⟩ := hbadR
            exact Or.inr (Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu he))
          · have hfwd := hωA.forall_exists_mem_spectrum_real_dist_le_of_resolvent_net
              hωB (N : Set ℝ) hη hC hcoverA (fun u hu =>
                le_of_not_gt (fun hh => hbadF ⟨u, hu, hh⟩)) herror
            have hrev := hωB.forall_exists_mem_spectrum_real_dist_le_of_resolvent_net
              hωA (M : Set ℝ) hη hC hcoverB (fun u hu =>
                le_of_not_gt (fun hh => hbadR ⟨u, hu, hh⟩)) herror
            exact False.elim (not_lt_of_ge
              (Metric.hausdorffDist_le_of_mem_dist (by positivity) hfwd hrev) hf)
      · exact Or.inl (Or.inl (Or.inr hcoverB))
    · exact Or.inl (Or.inl (Or.inl hcoverA))
  have hm : μ.real Bad ≤ μ.real (((LA ∪ LB) ∪ ⋃ u ∈ N, EF u) ∪ ⋃ u ∈ M, ER u) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  calc
    _ ≤ μ.real ((LA ∪ LB) ∪ ⋃ u ∈ N, EF u) + μ.real (⋃ u ∈ M, ER u) :=
      hm.trans (measureReal_union_le _ _)
    _ ≤ (μ.real (LA ∪ LB) + μ.real (⋃ u ∈ N, EF u)) + ∑ u ∈ M, μ.real (ER u) :=
      add_le_add (measureReal_union_le _ _) (measureReal_biUnion_finset_le M ER)
    _ ≤ _ := add_le_add
      (add_le_add (measureReal_union_le _ _) (measureReal_biUnion_finset_le N EF)) le_rfl

end MeasureTheory

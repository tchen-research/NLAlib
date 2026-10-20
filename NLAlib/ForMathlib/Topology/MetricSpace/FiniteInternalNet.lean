import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic.NormNum

/-! # Internal finite covers from external finite covers -/

noncomputable section
set_option autoImplicit false
open scoped NNReal ENNReal
namespace Metric

/-- An external finite cover gives an internal cover of at most the same
cardinality and twice the radius. This specializes Mathlib covering numbers
and includes empty sets and zero radius. -/
theorem exists_finset_subset_card_le_of_cover
    {X : Type*} [PseudoMetricSpace X] (S : Set X) (N : Finset X)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcover : ∀ x ∈ S, ∃ u ∈ N, dist x u ≤ ε) :
    ∃ M : Finset X, (M : Set X) ⊆ S ∧ M.card ≤ N.card ∧
      ∀ x ∈ S, ∃ u ∈ M, dist x u ≤ 2 * ε := by
  classical
  let e : ℝ≥0 := ⟨ε, hε⟩
  have hc : IsCover e S (N : Set X) := by
    apply IsCover.of_subset_iUnion_closedBall
    intro x hx
    obtain ⟨u, hu, hxu⟩ := hcover x hx
    exact Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu hxu)
  have hb : coveringNumber (2 * e) S ≤ (N.card : ℕ∞) :=
    (coveringNumber_two_mul_le_externalCoveringNumber e S).trans
      (by simpa using hc.externalCoveringNumber_le_encard)
  have htop : coveringNumber (2 * e) S ≠ ⊤ :=
    (lt_of_le_of_lt hb (by simp)).ne
  obtain ⟨C, hCS, hCf, hCc, hcard⟩ := exists_set_encard_eq_coveringNumber htop
  refine ⟨hCf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    exact hCS (hCf.mem_toFinset.mp hx)
  · have hh := hcard.trans_le hb
    rw [hCf.encard_eq_coe_toFinset_card] at hh
    exact_mod_cast hh
  · intro x hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (hCc.subset_iUnion_closedBall hx)
    obtain ⟨huC, hxu⟩ := Set.mem_iUnion.mp hu
    refine ⟨u, hCf.mem_toFinset.mpr huC, ?_⟩
    have hnum : ((2 * e : ℝ≥0) : ℝ) = 2 * ε := by rw [NNReal.coe_mul]; rfl
    change dist x u ≤ ((2 * e : ℝ≥0) : ℝ) at hxu
    rwa [hnum] at hxu

end Metric

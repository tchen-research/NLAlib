import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith

/-! # Filling the bounded complementary components of a compact set

The fill of a compact plane contour is its trace together with its bounded
complementary components. For a Jordan curve this is the usual closed
interior. Compactness of this set does not require Jordan separation:
complement components are open, while an outward ray from any point beyond
a ball containing the trace proves that point lies in an unbounded component.
-/

noncomputable section
open Bornology Metric Topology
namespace Set

section Topology
variable {X : Type*} [TopologicalSpace X] [Bornology X]

/-- Fill a set by adjoining its bounded complementary components. For a
Jordan curve in the plane, this is its trace together with its interior. -/
def boundedComplementFill (s : Set X) : Set X :=
  s ∪ {x | x ∉ s ∧ IsBounded (connectedComponentIn sᶜ x)}

/-- The original set is contained in its bounded-complement fill. -/
theorem subset_boundedComplementFill (s : Set X) : s ⊆ boundedComplementFill s :=
  subset_union_left

/-- A point outside the fill lies in an unbounded complementary component. -/
theorem not_mem_boundedComplementFill_iff {s : Set X} {x : X} :
    x ∉ boundedComplementFill s ↔ x ∉ s ∧ ¬ IsBounded (connectedComponentIn sᶜ x) := by
  by_cases hx : x ∈ s <;> simp [boundedComplementFill, hx]

/-- A complementary component through a point outside the fill stays outside
the fill, since all of its points determine the same component. -/
theorem connectedComponentIn_subset_compl_boundedComplementFill {s : Set X} {x : X}
    (hx : x ∉ boundedComplementFill s) :
    connectedComponentIn sᶜ x ⊆ (boundedComplementFill s)ᶜ := by
  obtain ⟨_, hx⟩ := not_mem_boundedComplementFill_iff.mp hx
  intro y hy
  refine not_mem_boundedComplementFill_iff.mpr ⟨connectedComponentIn_subset sᶜ x hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx

/-- Filling bounded components preserves closedness in a locally connected
space. Each complementary component left over is open. -/
theorem isClosed_boundedComplementFill [LocallyConnectedSpace X] {s : Set X}
    (hs : IsClosed s) : IsClosed (boundedComplementFill s) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' := (not_mem_boundedComplementFill_iff.mp hx).1
  exact Filter.mem_of_superset
    (hs.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx'))
    (connectedComponentIn_subset_compl_boundedComplementFill hx)

end Topology

section NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point beyond a ball containing a set belongs to an unbounded component
of its complement: the entire outward ray lies in that same component. -/
theorem not_isBounded_connectedComponentIn_compl_of_norm_lt
    {s : Set E} {R : ℝ} (hR : 0 ≤ R) (hs : s ⊆ closedBall 0 R)
    {x : E} (hx : R < ‖x‖) : ¬ IsBounded (connectedComponentIn sᶜ x) := by
  have hxpos : 0 < ‖x‖ := hR.trans_lt hx
  let ray : Set E := (fun t : ℝ => t • x) '' Ici 1
  have hray : IsPreconnected ray :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hxray : x ∈ ray := ⟨1, by simp, one_smul ℝ x⟩
  have hrays : ray ⊆ sᶜ := by
    rintro z ⟨t, ht, rfl⟩ hz
    change 1 ≤ t at ht
    have hb := hs hz
    rw [mem_closedBall_zero_iff] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht)] at hb
    nlinarith
  have hraycomp : ray ⊆ connectedComponentIn sᶜ x :=
    hray.subset_connectedComponentIn hxray hrays
  intro hcomp
  obtain ⟨M, hM⟩ := (hcomp.subset hraycomp).exists_norm_le
  let t : ℝ := (max M ‖x‖ + 1) / ‖x‖
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hxpos).mpr
    linarith [le_max_right M ‖x‖]
  have hn : ‖t • x‖ = max M ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht)]
    exact div_mul_cancel₀ _ hxpos.ne'
  have hb := hM (t • x) ⟨t, ht, rfl⟩
  rw [hn] at hb
  linarith [le_max_left M ‖x‖]

/-- Filling bounded complementary components does not enlarge a containing
closed ball. This applies in every real normed space. -/
theorem boundedComplementFill_subset_closedBall {s : Set E} {R : ℝ}
    (hR : 0 ≤ R) (hs : s ⊆ closedBall 0 R) :
    boundedComplementFill s ⊆ closedBall 0 R := by
  intro x hx
  by_contra hnot
  have hn : R < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hnot
  rcases hx with hx | ⟨_, hcomp⟩
  · exact hnot (hs hx)
  · exact not_isBounded_connectedComponentIn_compl_of_norm_lt hR hs hn hcomp

/-- Filling the bounded complementary components of a bounded set is bounded. -/
theorem isBounded_boundedComplementFill {s : Set E} (hs : IsBounded s) :
    IsBounded (boundedComplementFill s) := by
  obtain ⟨R, hR, hb⟩ := hs.exists_pos_norm_le
  exact isBounded_closedBall.subset
    (boundedComplementFill_subset_closedBall hR.le
      (fun x hx => mem_closedBall_zero_iff.mpr (hb x hx)))

/-- The fill of a compact set in a locally connected proper real normed space
is compact. In particular, every compact planar contour has compact fill. -/
theorem isCompact_boundedComplementFill [LocallyConnectedSpace E] [ProperSpace E]
    {s : Set E} (hs : IsCompact s) : IsCompact (boundedComplementFill s) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_boundedComplementFill hs.isClosed, isBounded_boundedComplementFill hs.isBounded⟩

/-- A holomorphy neighborhood of the compact filled trace contains an actual
positive closed metric buffer around it. -/
theorem exists_cthickening_boundedComplementFill_subset_open
    [LocallyConnectedSpace E] [ProperSpace E] {s U : Set E}
    (hs : IsCompact s) (hU : IsOpen U) (hsub : boundedComplementFill s ⊆ U) :
    ∃ δ, 0 < δ ∧ cthickening δ (boundedComplementFill s) ⊆ U :=
  (isCompact_boundedComplementFill hs).exists_cthickening_subset_open hU hsub

end NormedSpace
end Set

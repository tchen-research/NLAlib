import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import NLAlib.ForMathlib.Combinatorics.FiniteFlagEnumeration

/-!
# Finite flags containing prescribed heavy sets

A nested construction first includes all prescribed neighbors of its current
set, then includes the next prescribed row set. Padding gives exact, truncated
cardinalities at both stages. This is the finite combinatorial construction
underlying the rearrangement in Lemma 3.10 of Latała--van Handel--Youssef (2018).
-/

noncomputable section

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a finite set to the requested cardinality, truncated at the ambient
dimension. If the requested cardinality is smaller, retain the original set. -/
def extendToCard (s : Finset ι) (r : ℕ) : Finset ι :=
  if h : s.card ≤ min r (Fintype.card ι) then
    Classical.choose (exists_subsuperset_card_eq (subset_univ s) h
      (by simp : min r (Fintype.card ι) ≤ (univ : Finset ι).card))
  else s

omit [DecidableEq ι] in
/-- Cardinality padding always retains the original set. -/
theorem subset_extendToCard (s : Finset ι) (r : ℕ) : s ⊆ s.extendToCard r := by
  classical
  unfold extendToCard
  split_ifs with h
  · exact (Classical.choose_spec (exists_subsuperset_card_eq (subset_univ s) h
      (by simp : min r (Fintype.card ι) ≤ (univ : Finset ι).card))).1
  · exact Subset.rfl

omit [DecidableEq ι] in
/-- Padding has exactly the requested truncated cardinality when the original
set fits in the requested budget. -/
theorem card_extendToCard (s : Finset ι) {r : ℕ} (h : s.card ≤ r) :
    (s.extendToCard r).card = min r (Fintype.card ι) := by
  classical
  have h' : s.card ≤ min r (Fintype.card ι) := le_min h (card_le_univ s)
  rw [extendToCard, dif_pos h']
  exact (Classical.choose_spec (exists_subsuperset_card_eq (subset_univ s) h'
    (by simp : min r (Fintype.card ι) ≤ (univ : Finset ι).card))).2.2

/-- Include every prescribed neighbor of the selected indices, then pad. -/
def neighborExtension (s : Finset ι) (neighbors : ι → Finset ι) (r : ℕ) : Finset ι :=
  (s ∪ s.biUnion neighbors).extendToCard r

/-- Every original index belongs to the padded neighbor extension. -/
theorem subset_neighborExtension (s : Finset ι) (neighbors : ι → Finset ι) (r : ℕ) :
    s ⊆ s.neighborExtension neighbors r :=
  subset_union_left.trans (subset_extendToCard _ _)

/-- The extension contains the prescribed neighbors of every selected index. -/
theorem mem_neighborExtension {s : Finset ι} {neighbors : ι → Finset ι} {r : ℕ}
    {i j : ι} (hj : j ∈ s) (hi : i ∈ neighbors j) :
    i ∈ s.neighborExtension neighbors r := by
  exact subset_extendToCard _ _ (mem_union_right _ (mem_biUnion.mpr ⟨j, hj, hi⟩))

/-- A neighbor extension fits the union bound `|s| (1+c)`. -/
theorem card_neighborExtension (s : Finset ι) (neighbors : ι → Finset ι)
    {r c : ℕ} (hc : ∀ j ∈ s, (neighbors j).card ≤ c)
    (hr : s.card + s.card * c ≤ r) :
    (s.neighborExtension neighbors r).card = min r (Fintype.card ι) := by
  apply card_extendToCard
  exact (card_union_le _ _).trans
    ((Nat.add_le_add_left (card_biUnion_le_card_mul s neighbors c hc) _).trans hr)

/-- The main selected set at each level of a heavy-row/heavy-neighbor flag. -/
def heavyFlag (rows : ℕ → Finset ι) (neighbors : ℕ → ι → Finset ι)
    (N M : ℕ → ℕ) : ℕ → Finset ι
  | 0 => (rows 0).extendToCard (N 0)
  | k + 1 =>
      ((heavyFlag rows neighbors N M k).neighborExtension (neighbors k) (M k) ∪
        rows (k + 1)).extendToCard (N (k + 1))

/-- The intermediate neighbor set at a level of the flag. -/
def heavyNeighborFlag (rows : ℕ → Finset ι) (neighbors : ℕ → ι → Finset ι)
    (N M : ℕ → ℕ) (k : ℕ) : Finset ι :=
  (heavyFlag rows neighbors N M k).neighborExtension (neighbors k) (M k)

/-- The row sets are included in the main flag. -/
theorem subset_heavyFlag (rows : ℕ → Finset ι) (neighbors : ℕ → ι → Finset ι)
    (N M : ℕ → ℕ) (k : ℕ) : rows k ⊆ heavyFlag rows neighbors N M k := by
  cases k with
  | zero => exact subset_extendToCard _ _
  | succ k => exact subset_union_right.trans (subset_extendToCard _ _)

/-- Each main flag set lies in its intermediate neighbor set. -/
theorem heavyFlag_subset_heavyNeighborFlag (rows : ℕ → Finset ι)
    (neighbors : ℕ → ι → Finset ι) (N M : ℕ → ℕ) (k : ℕ) :
    heavyFlag rows neighbors N M k ⊆ heavyNeighborFlag rows neighbors N M k :=
  subset_neighborExtension _ _ _

/-- Each intermediate neighbor set lies in the next main flag set. -/
theorem heavyNeighborFlag_subset_heavyFlag_succ (rows : ℕ → Finset ι)
    (neighbors : ℕ → ι → Finset ι) (N M : ℕ → ℕ) (k : ℕ) :
    heavyNeighborFlag rows neighbors N M k ⊆ heavyFlag rows neighbors N M (k + 1) :=
  subset_union_left.trans (subset_extendToCard _ _)

/-- The main and intermediate flags have exact truncated cardinalities whenever
the row and neighbor budgets fit between successive prescribed cutoffs. -/
theorem card_heavyFlag_and_heavyNeighborFlag
    (rows : ℕ → Finset ι) (neighbors : ℕ → ι → Finset ι)
    (N M c : ℕ → ℕ) (hzero : (rows 0).card ≤ N 0)
    (hcol : ∀ k j, (neighbors k j).card ≤ c k)
    (hM : ∀ k, N k + N k * c k ≤ M k)
    (hN : ∀ k, M k + (rows (k + 1)).card ≤ N (k + 1)) :
    ∀ k, (heavyFlag rows neighbors N M k).card = min (N k) (Fintype.card ι) ∧
      (heavyNeighborFlag rows neighbors N M k).card = min (M k) (Fintype.card ι) := by
  intro k
  have hmain : ∀ k, (heavyFlag rows neighbors N M k).card =
      min (N k) (Fintype.card ι) := by
    intro k
    induction k with
    | zero => exact card_extendToCard _ hzero
    | succ k ih =>
        apply card_extendToCard
        have hcard : (heavyNeighborFlag rows neighbors N M k).card =
            min (M k) (Fintype.card ι) := by
          apply card_neighborExtension _ _ (fun j _ => hcol k j)
          calc
            _ ≤ N k + N k * c k := by rw [ih]; gcongr <;> exact min_le_left _ _
            _ ≤ M k := hM k
        apply (card_union_le _ _).trans
        change (heavyNeighborFlag rows neighbors N M k).card + _ ≤ _
        rw [hcard]
        exact (Nat.add_le_add_right (min_le_left _ _) _).trans (hN k)
  refine ⟨hmain k, ?_⟩
  apply card_neighborExtension _ _ (fun j _ => hcol k j)
  calc
    _ ≤ N k + N k * c k := by rw [hmain k]; gcongr <;> exact min_le_left _ _
    _ ≤ M k := hM k

/-- Interleave the main and intermediate flags into a single nested sequence. -/
def interleavedHeavyFlag (rows : ℕ → Finset ι) (neighbors : ℕ → ι → Finset ι)
    (N M : ℕ → ℕ) (t : ℕ) : Finset ι :=
  if t % 2 = 0 then heavyFlag rows neighbors N M (t / 2)
  else heavyNeighborFlag rows neighbors N M (t / 2)

/-- The interleaved heavy-set construction is a monotone finite-set flag. -/
theorem monotone_interleavedHeavyFlag (rows : ℕ → Finset ι)
    (neighbors : ℕ → ι → Finset ι) (N M : ℕ → ℕ) :
    Monotone (interleavedHeavyFlag rows neighbors N M) := by
  apply monotone_nat_of_le_succ
  intro t
  by_cases ht : t % 2 = 0
  · have ht' : (t + 1) % 2 ≠ 0 := by omega
    have hd : (t + 1) / 2 = t / 2 := by omega
    simp only [interleavedHeavyFlag, if_pos ht, if_neg ht', hd]
    exact heavyFlag_subset_heavyNeighborFlag rows neighbors N M _
  · have ht' : (t + 1) % 2 = 0 := by omega
    have hd : (t + 1) / 2 = t / 2 + 1 := by omega
    simp only [interleavedHeavyFlag, if_neg ht, if_pos ht', hd]
    exact heavyNeighborFlag_subset_heavyFlag_succ rows neighbors N M _

/-- One permutation simultaneously realizes every main and neighbor set up to
any finite truncation level as an exact initial segment. -/
theorem exists_equiv_fin_prefix_heavyFlag (rows : ℕ → Finset ι)
    (neighbors : ℕ → ι → Finset ι) (N M : ℕ → ℕ) (L : ℕ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, ∀ k ≤ L, ∀ i : Fin (Fintype.card ι),
      (e i ∈ heavyFlag rows neighbors N M k ↔
        i.val < (heavyFlag rows neighbors N M k).card) ∧
      (e i ∈ heavyNeighborFlag rows neighbors N M k ↔
        i.val < (heavyNeighborFlag rows neighbors N M k).card) := by
  let S : Fin (2 * L + 1 + 1) → Finset ι := fun t =>
    interleavedHeavyFlag rows neighbors N M t
  obtain ⟨e, he⟩ := exists_equiv_fin_prefix_of_monotone S
    ((monotone_interleavedHeavyFlag rows neighbors N M).comp (fun _ _ h => h))
  refine ⟨e, ?_⟩
  intro k hk i
  constructor
  · simpa [S, interleavedHeavyFlag] using he ⟨2 * k, by omega⟩ i
  · have hd : (2 * k + 1) / 2 = k := by omega
    simpa [S, interleavedHeavyFlag, hd] using he ⟨2 * k + 1, by omega⟩ i

end Finset

import NLAlib.ForMathlib.Analysis.FiniteHeavySets
import NLAlib.ForMathlib.Combinatorics.HeavySetFlags
import NLAlib.Matrix.Structured.ProfileRearrangementScales
import Mathlib.Data.Matrix.Basic

/-!
# One permutation controlling rows and heavy neighbors

The finite construction in Latała--van Handel--Youssef (2018), Lemma 3.10,
with exact double-exponential cutoffs. Heavy rows and heavy neighbors are
included in nested padded sets, and a single permutation makes all these
sets prefixes. No ordering or mask decomposition is assumed.
-/

noncomputable section

namespace NLAlib

variable {n : ℕ}

/-- Rows containing an entry above the logarithmic threshold at level `k`. -/
def profileHeavyRows (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) (k : ℕ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ j,
    b / Real.sqrt (Real.log (profilePreviousCutoff k)) < A i j

/-- Entries in a column above its energy threshold at level `k`. -/
def profileHeavyNeighbors (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (k : ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a / Real.sqrt (profilePreviousCutoff k) < A i j

/-- A logarithmic entry envelope bounds the number of heavy rows at every
level by the preceding double-exponential cutoff. -/
theorem card_profileHeavyRows_le (A : Matrix (Fin n) (Fin n) ℝ) {b : ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hb : ∀ i j, A i j * Real.sqrt (Real.log (i.val + 1)) ≤ b) (k : ℕ) :
    (profileHeavyRows A b k).card ≤ profilePreviousCutoff k := by
  classical
  unfold profileHeavyRows
  apply Finset.card_filter_le_of_imp_val_lt
  intro i hi
  obtain ⟨j, hj⟩ := hi
  by_contra hn
  exact (not_lt_of_ge (Finset.le_div_sqrt_log_of_weighted_le (fun i => A i j)
    (fun i => hA i j) (fun i => hb i j)
    (lt_of_lt_of_le (by decide : 1 < 2) (two_le_profilePreviousCutoff k))
    i (Nat.le_of_not_gt hn))) hj

/-- A column energy bound controls all heavy-neighbor sets, with a strict
cardinality inequality at the source's strict threshold. -/
theorem card_profileHeavyNeighbors_lt (A : Matrix (Fin n) (Fin n) ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hcol : ∀ j, ∑ i, A i j ^ 2 ≤ a ^ 2) (k : ℕ) (j : Fin n) :
    (profileHeavyNeighbors A a k j).card < profilePreviousCutoff k :=
  Finset.card_filter_div_sqrt_lt_of_sum_sq_le (fun i => A i j) ha (hcol j)
    (lt_of_lt_of_le (by decide : 0 < 2) (two_le_profilePreviousCutoff k))

/-- Simultaneously permute rows and columns so that entries in late rows are
bounded by a logarithmic envelope, and late cross entries are bounded by the
column energy. The construction is finite, includes zero/empty profiles, and
works at every cutoff, including cutoffs past the dimension. Source:
Latała--van Handel--Youssef (2018), Lemma 3.10; zero-based positions and
`profileCutoff 0 = 4` fix the boundary conventions explicitly. -/
theorem exists_equiv_entry_le_div_sqrt_log_and_div_sqrt
    (A : Matrix (Fin n) (Fin n) ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, 0 ≤ A i j) (hcol : ∀ j, ∑ i, A i j ^ 2 ≤ a ^ 2)
    (hb : ∀ i j, A i j * Real.sqrt (Real.log (i.val + 1)) ≤ b) :
    ∃ e : Fin n ≃ Fin n, ∀ k,
      (∀ i j, profileCutoff k ≤ i.val →
        A (e i) (e j) ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k))) ∧
      (∀ i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
        A (e i) (e j) ≤ a / Real.sqrt (profilePreviousCutoff k)) := by
  classical
  let rows := profileHeavyRows A b
  let neighbors := profileHeavyNeighbors A a
  let I := Finset.heavyFlag rows neighbors profileCutoff profileNeighborCutoff
  let J := Finset.heavyNeighborFlag rows neighbors profileCutoff profileNeighborCutoff
  have hrow (k : ℕ) : (rows k).card ≤ profilePreviousCutoff k :=
    card_profileHeavyRows_le A hA hb k
  have hneighbor (k : ℕ) (j : Fin n) :
      (neighbors k j).card ≤ profilePreviousCutoff k :=
    (card_profileHeavyNeighbors_lt A ha hcol k j).le
  have hcards (k : ℕ) : (I k).card = min (profileCutoff k) n ∧
      (J k).card = min (profileNeighborCutoff k) n := by
    simpa only [Fintype.card_fin] using
      Finset.card_heavyFlag_and_heavyNeighborFlag rows neighbors
        profileCutoff profileNeighborCutoff profilePreviousCutoff
        ((hrow 0).trans (profilePreviousCutoff_le 0)) hneighbor
        (fun _ => le_rfl) (fun k =>
          (Nat.add_le_add_left (hrow (k + 1)) _).trans
            (profileNeighborCutoff_add_previous_succ_le k)) k
  obtain ⟨e, he⟩ := Finset.exists_equiv_fin_prefix_heavyFlag rows neighbors
    profileCutoff profileNeighborCutoff n
  let e' : Fin n ≃ Fin n := (finCongr (Fintype.card_fin n).symm).trans e
  have he' (k : ℕ) (hk : k ≤ n) (i : Fin n) :
      (e' i ∈ I k ↔ i.val < (I k).card) ∧
      (e' i ∈ J k ↔ i.val < (J k).card) := by
    exact he k hk (finCongr (Fintype.card_fin n).symm i)
  refine ⟨e', ?_⟩
  intro k
  constructor
  · intro i j hi
    by_cases hk : k ≤ n
    · have hout : e' i ∉ I k := by
        rw [(he' k hk i).1, (hcards k).1]
        omega
      by_contra hlt
      apply hout
      apply Finset.subset_heavyFlag rows neighbors profileCutoff profileNeighborCutoff k
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e' j, lt_of_not_ge hlt⟩⟩
    · have hlarge := le_profileCutoff k
      omega
  · intro i j hi hj
    by_cases hk : k ≤ n
    · have hin : e' j ∈ I k := by
        rw [(he' k hk j).1, (hcards k).1]
        exact lt_min hj j.isLt
      have hout : e' i ∉ J k := by
        rw [(he' k hk i).2, (hcards k).2]
        omega
      by_contra hlt
      apply hout
      exact Finset.mem_neighborExtension hin
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hlt⟩)
    · have hlarge := (le_profileCutoff k).trans (profileCutoff_le_neighborCutoff k)
      omega

end NLAlib

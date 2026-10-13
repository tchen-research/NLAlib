import NLAlib.Matrix.Inequalities.MajorizationWeights

/-!
# Majorization of finite real vectors

The sum of the largest coordinates is defined by a descending sort, and is
characterized intrinsically as the attained maximum over subsets of a prescribed
cardinality. Thus the definitions work over any finite index type, including the
empty type. Source: Marshall–Olkin–Arnold (2011), Definitions 1.A.1–1.A.2.
Atlas: `majorization-def`.
-/

noncomputable section

namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-- An enumeration of a finite real vector in decreasing value order. Ties are
resolved by Mathlib's canonical tuple sort; only its value order matters. -/
def sortingEquiv (x : ι → ℝ) : Fin (Fintype.card ι) ≃ ι :=
  (Tuple.sort (fun i : Fin (Fintype.card ι) =>
    -x ((Fintype.equivFin ι).symm i))).trans (Fintype.equivFin ι).symm

/-- The decreasingly sorted value list of a finite real vector. -/
def sortedVector (x : ι → ℝ) : Fin (Fintype.card ι) → ℝ := x ∘ sortingEquiv x

/-- The sum of the largest `k` entries. When `k` exceeds the dimension this is
the full sum, and `k = 0` gives zero. Marshall–Olkin–Arnold, Definitions 1.A.1–1.A.2.
atlas: majorization-def -/
def sumLargest (x : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card ι), if i.val < k then sortedVector x i else 0

/-- Weak majorization compares every nonempty prefix of the descending value
lists; the equivalent subset formulation is index independent.
Marshall–Olkin–Arnold, Definition 1.A.2.
atlas: majorization-def -/
def WeaklyMajorized (x y : ι → ℝ) : Prop :=
  ∀ k ≤ Fintype.card ι, sumLargest x k ≤ sumLargest y k

/-- Ordinary majorization is weak majorization together with equality of the
full coordinate totals. Marshall–Olkin–Arnold, Definition 1.A.1.
atlas: majorization-def -/
def Majorized (x y : ι → ℝ) : Prop :=
  WeaklyMajorized x y ∧ (∑ i, x i) = ∑ i, y i

/-- The canonical sorted value list is decreasing. -/
theorem sortedVector_antitone (x : ι → ℝ) : Antitone (sortedVector x) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i : Fin (Fintype.card ι) =>
    -x ((Fintype.equivFin ι).symm i)) hij
  simpa only [sortedVector, sortingEquiv, Equiv.coe_trans, Function.comp_def,
    neg_le_neg_iff] using h

/-- Sorting does not change a coordinate sum, with any scalar function applied
to the coordinates. -/
theorem sum_sortedVector (x : ι → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (sortedVector x i)) = ∑ i, f (x i) :=
  (sortingEquiv x).sum_comp (fun i => f (x i))

/-- The empty prefix is zero. -/
@[simp] theorem sumLargest_zero (x : ι → ℝ) : sumLargest x 0 = 0 := by
  simp [sumLargest]

/-- A prefix of at least the dimension is the full coordinate sum. -/
theorem sumLargest_eq_sum_of_card_le (x : ι → ℝ) {k : ℕ}
    (hk : Fintype.card ι ≤ k) : sumLargest x k = ∑ i, x i := by
  simp only [sumLargest, if_pos (lt_of_lt_of_le (Fin.isLt _) hk)]
  exact sum_sortedVector x id

/-- A finite subset sum is bounded by the sum of that many largest entries.
Marshall–Olkin–Arnold (2011), the subset version of the prefix criterion. -/
theorem sum_le_sumLargest [DecidableEq ι] (x : ι → ℝ) (S : Finset ι) :
    (∑ i ∈ S, x i) ≤ sumLargest x S.card := by
  classical
  let w : Fin (Fintype.card ι) → ℝ := fun i => if sortingEquiv x i ∈ S then 1 else 0
  have hw : (∑ i, w i) = (S.card : ℝ) := by
    change (∑ i, (fun j : ι => if j ∈ S then (1 : ℝ) else 0) (sortingEquiv x i)) = _
    rw [(sortingEquiv x).sum_comp (fun j : ι => if j ∈ S then (1 : ℝ) else 0)]
    simp
  have hsum : (∑ i, sortedVector x i * w i) = ∑ i ∈ S, x i := by
    change (∑ i, (fun j : ι => x j * (if j ∈ S then 1 else 0)) (sortingEquiv x i)) = _
    rw [(sortingEquiv x).sum_comp (fun j : ι => x j * (if j ∈ S then (1 : ℝ) else 0))]
    simp
  rw [← hsum]
  exact sum_mul_le_sum_ite_lt_of_antitone_of_sum_eq (sortedVector x) w
    (sortedVector_antitone x) (fun i => by dsimp [w]; split <;> positivity)
    (fun i => by dsimp [w]; split <;> norm_num) (Finset.card_le_univ S) hw

/-- The set of the `k` largest coordinates, with deterministic tie breaking. -/
def largestCoordinates [DecidableEq ι] (x : ι → ℝ) (k : ℕ) : Finset ι :=
  ((Finset.univ : Finset (Fin (Fintype.card ι))).filter fun i => i.val < k).map
    (sortingEquiv x).toEmbedding

/-- The attaining largest-coordinate set has cardinality `k` for `k` in range. -/
theorem card_largestCoordinates [DecidableEq ι] (x : ι → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card ι) : (largestCoordinates x k).card = k := by
  simp [largestCoordinates, card_filter_fin_lt hk]

/-- The largest-coordinate set attains the descending prefix sum. -/
theorem sum_largestCoordinates [DecidableEq ι] (x : ι → ℝ) (k : ℕ) :
    (∑ i ∈ largestCoordinates x k, x i) = sumLargest x k := by
  classical
  simp only [largestCoordinates, Finset.sum_map, Equiv.toEmbedding_apply,
    Finset.sum_filter, sumLargest, sortedVector, Function.comp_apply]

/-- The top-coordinate sum is the attained maximum over subsets of cardinality
`k`, including the empty and full endpoints. -/
theorem isGreatest_sumLargest [DecidableEq ι] (x : ι → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    IsGreatest {z : ℝ | ∃ S : Finset ι, S.card = k ∧ (∑ i ∈ S, x i) = z}
      (sumLargest x k) := by
  refine ⟨⟨largestCoordinates x k, card_largestCoordinates x hk,
    sum_largestCoordinates x k⟩, ?_⟩
  rintro z ⟨S, hS, rfl⟩
  simpa [hS] using sum_le_sumLargest x S

/-- Weak majorization is equivalently the family of all subset-sum comparisons
against the corresponding top-coordinate sum. -/
theorem weaklyMajorized_iff_sum_le [DecidableEq ι] (x y : ι → ℝ) :
    WeaklyMajorized x y ↔ ∀ S : Finset ι, (∑ i ∈ S, x i) ≤ sumLargest y S.card := by
  constructor
  · intro h S
    exact (sum_le_sumLargest x S).trans (h S.card (Finset.card_le_univ S))
  · intro h k hk
    have hS := h (largestCoordinates x k)
    rwa [card_largestCoordinates x hk, sum_largestCoordinates x k] at hS

/-- Weak majorization is reflexive. -/
theorem WeaklyMajorized.refl (x : ι → ℝ) : WeaklyMajorized x x := fun _ _ => le_rfl

/-- Weak majorization is transitive. -/
theorem WeaklyMajorized.trans {x y z : ι → ℝ} (hxy : WeaklyMajorized x y)
    (hyz : WeaklyMajorized y z) : WeaklyMajorized x z := fun k hk => (hxy k hk).trans (hyz k hk)

/-- Ordinary majorization is reflexive. -/
theorem Majorized.refl (x : ι → ℝ) : Majorized x x := ⟨WeaklyMajorized.refl x, rfl⟩

/-- Ordinary majorization is transitive. -/
theorem Majorized.trans {x y z : ι → ℝ} (hxy : Majorized x y)
    (hyz : Majorized y z) : Majorized x z := ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

end NLAlib

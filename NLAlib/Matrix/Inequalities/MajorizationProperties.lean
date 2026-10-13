import NLAlib.Matrix.Inequalities.MajorizationStochastic
/-!
# Prefix and permutation API for majorization

Intrinsic top-coordinate sums agree with ordinary prefixes for a descending
list. They are invariant under relabeling, and are subadditive.
Source: Marshall–Olkin–Arnold (2011), Chapters 1–2.
-/

noncomputable section

namespace NLAlib

/-- A finite prefix selected by a bound equals the sum on the shorter coordinate
type, embedded into the full list. Includes zero and full prefixes. -/
theorem sum_fin_ite_lt_eq_sum_castLE {n k : ℕ} (hk : k ≤ n) (a : Fin n → ℝ) :
    (∑ i : Fin n, if i.val < k then a i else 0) = ∑ i : Fin k, a (Fin.castLE hk i) := by
  classical
  have he : (Finset.univ : Finset (Fin k)).map (Fin.castLEEmb hk) =
      (Finset.univ : Finset (Fin n)).filter fun i => i.val < k := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      exact j.isLt
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  rw [← Finset.sum_filter, ← he, Finset.sum_map]
  rfl

/-- On an already decreasing list, the largest-coordinate sum is its prefix.
The formula also holds beyond the dimension, where both sides are full sums. -/
theorem sumLargest_eq_prefix_of_antitone {n : ℕ} (a : Fin n → ℝ) (ha : Antitone a)
    (k : ℕ) : sumLargest a k = ∑ i : Fin n, if i.val < k then a i else 0 := by
  classical
  by_cases hk : k ≤ n
  · have bound (S : Finset (Fin n)) (hS : S.card = k) :
        (∑ i ∈ S, a i) ≤ ∑ i : Fin n, if i.val < k then a i else 0 := by
      let w : Fin n → ℝ := fun i => if i ∈ S then 1 else 0
      have hw : (∑ i, w i) = (k : ℝ) := by simp [w, hS]
      have hb := sum_mul_le_sum_ite_lt_of_antitone_of_sum_eq a w ha
        (fun i => by dsimp [w]; split <;> positivity)
        (fun i => by dsimp [w]; split <;> norm_num) hk hw
      simpa [w] using hb
    apply le_antisymm
    · rw [← sum_largestCoordinates a k]
      exact bound _ (card_largestCoordinates a (by simpa using hk))
    · let S := (Finset.univ : Finset (Fin n)).filter fun i => i.val < k
      have hS : S.card = k := card_filter_fin_lt hk
      have hb := sum_le_sumLargest a S
      simpa only [S, Finset.sum_filter, hS] using hb
  · have hn : n ≤ k := by omega
    rw [sumLargest_eq_sum_of_card_le a (by simpa using hn)]
    simp only [if_pos (lt_of_lt_of_le (Fin.isLt _) hn)]

/-- A coordinate permutation is majorized by the original vector, including
equality of totals. Source: a permutation matrix is doubly stochastic. -/
theorem majorized_comp_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (σ : Equiv.Perm ι) : Majorized (x ∘ σ) x := by
  simpa only [Matrix.permMatrix_mulVec] using
    majorized_mulVec_of_doublyStochastic x (permMatrix_mem_doublyStochastic (σ := σ))

/-- Permuting coordinates does not change a largest-coordinate sum. -/
theorem sumLargest_comp_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (σ : Equiv.Perm ι) (k : ℕ) : sumLargest (x ∘ σ) k = sumLargest x k := by
  by_cases hk : k ≤ Fintype.card ι
  · have h1 := (majorized_comp_perm x σ).1 k hk
    have h2 := (majorized_comp_perm (x ∘ σ) σ.symm).1 k hk
    simp only [Function.comp_def, Equiv.apply_symm_apply] at h2
    exact le_antisymm h1 h2
  · rw [sumLargest_eq_sum_of_card_le _ (by omega), sumLargest_eq_sum_of_card_le _ (by omega)]
    exact Equiv.sum_comp σ x

/-- The largest-coordinate sum is subadditive, including signed coordinates
and both prefix endpoints. Marshall–Olkin–Arnold (2011), Chapter 1. -/
theorem sumLargest_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (k : ℕ) : sumLargest (x + y) k ≤ sumLargest x k + sumLargest y k := by
  by_cases hk : k ≤ Fintype.card ι
  · let S := largestCoordinates (x + y) k
    have hS : S.card = k := card_largestCoordinates _ hk
    rw [← sum_largestCoordinates (x + y) k]
    change (∑ i ∈ S, (x i + y i)) ≤ _
    rw [Finset.sum_add_distrib]
    simpa only [hS] using add_le_add (sum_le_sumLargest x S) (sum_le_sumLargest y S)
  · rw [sumLargest_eq_sum_of_card_le _ (by omega), sumLargest_eq_sum_of_card_le _ (by omega),
      sumLargest_eq_sum_of_card_le _ (by omega)]
    simp [Finset.sum_add_distrib]

/-- Ordinary majorization gives the corresponding bottom-subset bound by
applying the top-subset criterion to the complementary coordinates.
This signed form includes empty and full subsets. -/
theorem Majorized.sum_sub_sumLargest_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x y : ι → ℝ} (hxy : Majorized x y) (S : Finset ι) :
    (∑ i, y i) - sumLargest y (Fintype.card ι - S.card) ≤ ∑ i ∈ S, x i := by
  have hcomp := (weaklyMajorized_iff_sum_le x y).mp hxy.1 Sᶜ
  have hsum : (∑ i ∈ S, x i) + (∑ i ∈ Sᶜ, x i) = ∑ i, y i :=
    (Finset.sum_add_sum_compl S x).trans hxy.2
  rw [Finset.card_compl] at hcomp
  linarith

end NLAlib

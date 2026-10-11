import NLAlib.Matrix.MajorizationHLP
import NLAlib.Matrix.MajorizationProperties

/-!
# Hinge-function characterization of majorization

Top-coordinate sums are recovered from the functions `u ↦ max (u - a) 0`.
This proves the converse convex-function tests with exact prefix endpoints.
Source: Marshall–Olkin–Arnold (2011), Propositions 4.B.1–4.B.2.
Atlas: `majorization-def`.
-/

noncomputable section
open scoped BigOperators

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every top-coordinate sum is bounded by the shifted hinge sum. -/
theorem sumLargest_le_card_mul_add_sum_max_sub (x : ι → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card ι) (a : ℝ) :
    sumLargest x k ≤ (k : ℝ) * a + ∑ i, max (x i - a) 0 := by
  have hp (i : Fin (Fintype.card ι)) :
      (if i.val < k then sortedVector x i else 0) ≤
        (if i.val < k then a else 0) + max (sortedVector x i - a) 0 := by
    by_cases hi : i.val < k
    · simp only [if_pos hi]
      linarith [le_max_left (sortedVector x i - a) 0]
    · simp only [if_neg hi, zero_add]
      exact le_max_right _ _
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  rw [Finset.sum_add_distrib] at h
  have hcard : (∑ i : Fin (Fintype.card ι), if i.val < k then a else 0) = (k : ℝ) * a := by
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_fin_lt hk]
    simp [nsmul_eq_mul]
  rwa [hcard, sum_sortedVector x (fun z => max (z - a) 0)] at h

omit [DecidableEq ι] in
/-- At an ordered coordinate threshold, the top-coordinate upper bound is
attained. Every prefix from zero to full dimension is included. -/
theorem exists_sumLargest_eq_card_mul_add_sum_max_sub (y : ι → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    ∃ a : ℝ, sumLargest y k = (k : ℝ) * a + ∑ i, max (y i - a) 0 := by
  classical
  by_cases hn : Fintype.card ι = 0
  · have hk0 : k = 0 := by omega
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    refine ⟨0, ?_⟩
    simp [hk0]
  · have hnpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hn
    let a : ℝ := if h : k < Fintype.card ι then sortedVector y ⟨k, h⟩
      else sortedVector y ⟨Fintype.card ι - 1, by omega⟩
    have hlow (i : Fin (Fintype.card ι)) (hi : i.val < k) : a ≤ sortedVector y i := by
      dsimp [a]
      split_ifs with h
      · exact sortedVector_antitone y (show i ≤ (⟨k, h⟩ : Fin _) from by
          change i.val ≤ k; omega)
      · exact sortedVector_antitone y (show i ≤ (⟨Fintype.card ι - 1, by omega⟩ : Fin _) from by
          change i.val ≤ Fintype.card ι - 1; omega)
    have hhigh (i : Fin (Fintype.card ι)) (hi : ¬ i.val < k) : sortedVector y i ≤ a := by
      dsimp [a]
      split_ifs with h
      · exact sortedVector_antitone y (show (⟨k, h⟩ : Fin _) ≤ i from by
          change k ≤ i.val; omega)
      · omega
    have he (i : Fin (Fintype.card ι)) : max (sortedVector y i - a) 0 =
        if i.val < k then sortedVector y i - a else 0 := by
      by_cases hi : i.val < k
      · rw [if_pos hi, max_eq_left (sub_nonneg.mpr (hlow i hi))]
      · rw [if_neg hi, max_eq_right (sub_nonpos.mpr (hhigh i hi))]
    have hsum : (∑ i : Fin (Fintype.card ι), if i.val < k then sortedVector y i - a else 0) =
        sumLargest y k - (k : ℝ) * a := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, card_filter_fin_lt hk]
      simp only [sumLargest, ← Finset.sum_filter, nsmul_eq_mul]
    refine ⟨a, ?_⟩
    rw [← sum_sortedVector y (fun z => max (z - a) 0)]
    simp_rw [he]
    rw [hsum]
    ring

omit [DecidableEq ι] in
/-- Hinge inequalities imply all weak-majorization prefix inequalities.
Marshall–Olkin–Arnold (2011), Proposition 4.B.2.
atlas: majorization-def (partial) -/
theorem weaklyMajorized_of_sum_max_sub_le {x y : ι → ℝ}
    (h : ∀ a : ℝ, (∑ i, max (x i - a) 0) ≤ ∑ i, max (y i - a) 0) :
    WeaklyMajorized x y := by
  intro k hk
  obtain ⟨a, ha⟩ := exists_sumLargest_eq_card_mul_add_sum_max_sub y hk
  calc
    sumLargest x k ≤ (k : ℝ) * a + ∑ i, max (x i - a) 0 :=
      sumLargest_le_card_mul_add_sum_max_sub x hk a
    _ ≤ (k : ℝ) * a + ∑ i, max (y i - a) 0 := by linarith [h a]
    _ = sumLargest y k := ha.symm

/-- Weak majorization implies every hinge-sum inequality. This direct subset
proof does not presuppose the increasing-convex characterization. -/
theorem WeaklyMajorized.sum_max_sub_le {x y : ι → ℝ} (hxy : WeaklyMajorized x y) (a : ℝ) :
    (∑ i, max (x i - a) 0) ≤ ∑ i, max (y i - a) 0 := by
  classical
  let S := (Finset.univ : Finset ι).filter fun i => a < x i
  have hsum : (∑ i, max (x i - a) 0) = (∑ i ∈ S, x i) - (S.card : ℝ) * a := by
    have he (i : ι) : max (x i - a) 0 = if a < x i then x i - a else 0 := by
      by_cases hi : a < x i
      · rw [if_pos hi, max_eq_left (by linarith)]
      · rw [if_neg hi, max_eq_right (by linarith)]
    simp_rw [he]
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const]
    simp [S, nsmul_eq_mul]
  rw [hsum]
  have hS := (weaklyMajorized_iff_sum_le x y).mp hxy S
  have hy := sumLargest_le_card_mul_add_sum_max_sub y (Finset.card_le_univ S) a
  linarith

/-- Weak majorization is exactly comparison of all translated positive-part
sums, including the degenerate empty coordinate space. -/
theorem weaklyMajorized_iff_sum_max_sub_le (x y : ι → ℝ) :
    WeaklyMajorized x y ↔
      ∀ a : ℝ, (∑ i, max (x i - a) 0) ≤ ∑ i, max (y i - a) 0 :=
  ⟨fun h => h.sum_max_sub_le, weaklyMajorized_of_sum_max_sub_le⟩

end NLAlib

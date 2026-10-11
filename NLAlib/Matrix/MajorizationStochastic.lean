import NLAlib.Matrix.Majorization

/-!
# Doubly stochastic maps and majorization

The finite weight-budget proof that a doubly stochastic image is majorized by its
input, with no sign assumption. Source: Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
Atlas: `majorization-def`.
-/

noncomputable section
open scoped BigOperators Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Arbitrary finite-index signed weight budget, in the intrinsic top-coordinate
sum vocabulary. Marshall–Olkin–Arnold (2011), prefix-weight lemma. -/
theorem sum_mul_le_sumLargest (x w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) {k : ℕ} (hk : k ≤ Fintype.card ι)
    (hbudget : ∑ i, w i = (k : ℝ)) : (∑ i, x i * w i) ≤ sumLargest x k := by
  rw [← (sortingEquiv x).sum_comp (fun i => x i * w i)]
  exact sum_mul_le_sum_ite_lt_of_antitone_of_sum_eq (sortedVector x)
    (w ∘ sortingEquiv x) (sortedVector_antitone x) (fun i => hw0 _)
    (fun i => hw1 _) hk (by simpa only [Function.comp_apply] using
      ((sortingEquiv x).sum_comp w).trans hbudget)

/-- A doubly stochastic map weakly majorizes its image, without a sign
restriction on the input vector. Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
atlas: majorization-def (partial) -/
theorem weaklyMajorized_mulVec_of_doublyStochastic (y : ι → ℝ)
    {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι) : WeaklyMajorized (D *ᵥ y) y := by
  classical
  rw [weaklyMajorized_iff_sum_le]
  intro S
  let w : ι → ℝ := fun j => ∑ i ∈ S, D i j
  have hw0 (j : ι) : 0 ≤ w j :=
    Finset.sum_nonneg fun i _ => nonneg_of_mem_doublyStochastic hD
  have hw1 (j : ι) : w j ≤ 1 := by
    rw [← sum_col_of_mem_doublyStochastic hD j]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => nonneg_of_mem_doublyStochastic hD)
  have hw : (∑ j, w j) = (S.card : ℝ) := by
    dsimp [w]
    rw [Finset.sum_comm]
    simp only [sum_row_of_mem_doublyStochastic hD]
    simp
  have hsum : (∑ i ∈ S, (D *ᵥ y) i) = ∑ j, y j * w j := by
    simp only [Matrix.mulVec, dotProduct, w]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum, mul_comm]
  rw [hsum]
  exact sum_mul_le_sumLargest y w hw0 hw1 (Finset.card_le_univ S) hw

/-- A doubly stochastic image is majorized by its input, including equality
of totals. Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
atlas: majorization-def (partial) -/
theorem majorized_mulVec_of_doublyStochastic (y : ι → ℝ)
    {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι) : Majorized (D *ᵥ y) y :=
  ⟨weaklyMajorized_mulVec_of_doublyStochastic y hD,
    sum_mulVec_of_mem_doublyStochastic hD⟩

omit [DecidableEq ι] in
/-- The signed bottom-weight budget follows from applying the top-weight
budget to `1 - w`. All exact integer masses from zero to dimension are included. -/
theorem sum_sub_sumLargest_le_sum_mul (x w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) {k : ℕ} (hk : k ≤ Fintype.card ι)
    (hbudget : ∑ i, w i = (k : ℝ)) :
    (∑ i, x i) - sumLargest x (Fintype.card ι - k) ≤ ∑ i, x i * w i := by
  have hmass : (∑ i, (1 - w i)) = ((Fintype.card ι - k : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hbudget, Nat.cast_sub hk]
    simp
  have h := sum_mul_le_sumLargest x (fun i => 1 - w i)
    (fun i => sub_nonneg.mpr (hw1 i)) (fun i => by linarith [hw0 i])
    (Nat.sub_le _ _) hmass
  have he : (∑ i, x i * (1 - w i)) = (∑ i, x i) - ∑ i, x i * w i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [he] at h
  linarith

end NLAlib

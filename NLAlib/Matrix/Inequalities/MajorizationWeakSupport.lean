import NLAlib.Matrix.Inequalities.MajorizationSupport
/-!
# Nonnegative support bounds for weak majorization

Abel summation with nonnegative decreasing weights needs no equality of totals.
This is the support-function route to the increasing-convex criterion.
Source: Marshall–Olkin–Arnold (2011), Proposition 4.B.2.
-/

noncomputable section

namespace NLAlib

/-- Nonnegative decreasing weights preserve every prefix-sum domination, without
assuming equality of totals. Finite Abel summation. -/
theorem sum_mul_le_of_nonneg_of_prefix_le {n : ℕ} (a b c : Fin n → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : Antitone a)
    (hp : ∀ k ≤ n, (∑ i : Fin n, if i.val < k then b i else 0) ≤
      ∑ i : Fin n, if i.val < k then c i else 0) :
    (∑ i, a i * b i) ≤ ∑ i, a i * c i := by
  classical
  let s : ℕ → ℝ := fun i => if hi : i < n then a ⟨i, hi⟩ else 0
  let d : ℕ → ℝ := fun i => if hi : i < n then b ⟨i, hi⟩ else 0
  let t : ℕ → ℝ := fun i => if hi : i < n then c ⟨i, hi⟩ else 0
  have hs0 (i : ℕ) : 0 ≤ s i := by dsimp [s]; split_ifs <;> simp [ha0]
  have hs : Antitone s := by
    intro i j hij
    by_cases hj : j < n
    · have hi : i < n := lt_of_le_of_lt hij hj
      simp only [s, dif_pos hi, dif_pos hj]
      exact ha hij
    · simp only [s, dif_neg hj]
      exact hs0 i
  have hprefix : ∀ k ≤ n, (∑ i ∈ Finset.range k, d i) ≤ ∑ i ∈ Finset.range k, t i := by
    intro k hk
    have h := hp k hk
    have hd := sum_fin_ite_lt_eq_sum_range hk d
    have hc := sum_fin_ite_lt_eq_sum_range hk t
    simp only [d, t, dif_pos (Fin.isLt _)] at hd hc
    rwa [← hd, ← hc]
  have h := sum_range_mul_le_of_partial_le hs0 hs hprefix
  rw [← Fin.sum_univ_eq_sum_range (fun i => s i * d i) n,
    ← Fin.sum_univ_eq_sum_range (fun i => s i * t i) n] at h
  simpa only [s, d, t, dif_pos (Fin.isLt _)] using h

/-- Weak majorization bounds the pairing with every nonnegative sorted weight
list. Marshall–Olkin–Arnold (2011), the support criterion. -/
theorem WeaklyMajorized.sum_sortedVector_mul_le {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} (hxy : WeaklyMajorized x y) (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) :
    (∑ i, sortedVector a i * sortedVector x i) ≤
      ∑ i, sortedVector a i * sortedVector y i :=
  sum_mul_le_of_nonneg_of_prefix_le _ _ _ (fun i => ha0 (sortingEquiv a i))
    (sortedVector_antitone a) hxy

/-- Every nonnegative coordinate pairing of a weakly majorized vector is
dominated by a permutation of the comparator. -/
theorem WeaklyMajorized.exists_perm_sum_mul_le {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} (hxy : WeaklyMajorized x y) (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) :
    ∃ σ : Equiv.Perm ι, (∑ i, a i * x i) ≤ ∑ i, a i * y (σ i) := by
  let σ : Equiv.Perm ι := (sortingEquiv a).symm.trans (sortingEquiv y)
  refine ⟨σ, ?_⟩
  calc
    (∑ i, a i * x i) ≤ ∑ i, sortedVector a i * sortedVector x i :=
      sum_mul_le_sum_sortedVector_mul a x
    _ ≤ ∑ i, sortedVector a i * sortedVector y i := hxy.sum_sortedVector_mul_le a ha0
    _ = ∑ i, a i * y (σ i) := by
      rw [← (sortingEquiv a).sum_comp (fun i => a i * y (σ i))]
      simp [sortedVector, σ]

end NLAlib

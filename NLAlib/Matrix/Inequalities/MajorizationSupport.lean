import NLAlib.Matrix.Inequalities.MajorizationStochastic
import NLAlib.Matrix.Inequalities.VonNeumann
/-!
# Support functions of permutation orbits

Rearrangement and Abel summation characterize the linear support bounds of
majorization. These avoid a coordinate-peeling induction in the HLP converse.
Source: Marshall–Olkin–Arnold (2011), Chapters 2–4.
-/

noncomputable section
open scoped BigOperators

namespace NLAlib

/-- Signed Abel summation: exact total equality allows arbitrary decreasing
real weights, and prefix domination implies domination of their pairings.
Marshall–Olkin–Arnold (2011), majorization support criterion. -/
theorem sum_mul_le_of_prefix_le_of_sum_eq {n : ℕ} (a b c : Fin n → ℝ)
    (ha : Antitone a)
    (hp : ∀ k ≤ n, (∑ i : Fin n, if i.val < k then b i else 0) ≤
      ∑ i : Fin n, if i.val < k then c i else 0)
    (ht : (∑ i, b i) = ∑ i, c i) : (∑ i, a i * b i) ≤ ∑ i, a i * c i := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    let v := a (Fin.last n)
    let s : ℕ → ℝ := fun i => if hi : i < n + 1 then a ⟨i, hi⟩ - v else 0
    let d : ℕ → ℝ := fun i => if hi : i < n + 1 then b ⟨i, hi⟩ else 0
    let t : ℕ → ℝ := fun i => if hi : i < n + 1 then c ⟨i, hi⟩ else 0
    have hs0 (i : ℕ) : 0 ≤ s i := by
      dsimp [s]
      split_ifs with hi
      · exact sub_nonneg.mpr (ha (Fin.le_last _))
      · exact le_rfl
    have hs : Antitone s := by
      intro i j hij
      by_cases hj : j < n + 1
      · have hi : i < n + 1 := lt_of_le_of_lt hij hj
        simp only [s, dif_pos hi, dif_pos hj]
        exact sub_le_sub_right (ha hij) v
      · simp only [s, dif_neg hj]
        exact hs0 i
    have hprefix : ∀ k ≤ n + 1,
        (∑ i ∈ Finset.range k, d i) ≤ ∑ i ∈ Finset.range k, t i := by
      intro k hk
      have h := hp k hk
      have hd := sum_fin_ite_lt_eq_sum_range hk d
      have hc := sum_fin_ite_lt_eq_sum_range hk t
      simp only [d, t, dif_pos (Fin.isLt _)] at hd hc
      rwa [← hd, ← hc]
    have h := sum_range_mul_le_of_partial_le hs0 hs hprefix
    rw [← Fin.sum_univ_eq_sum_range (fun i => s i * d i) (n + 1),
      ← Fin.sum_univ_eq_sum_range (fun i => s i * t i) (n + 1)] at h
    simp only [s, d, t, dif_pos (Fin.isLt _)] at h
    have hb : (∑ i, (a i - v) * b i) = (∑ i, a i * b i) - v * ∑ i, b i := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    have hc : (∑ i, (a i - v) * c i) = (∑ i, a i * c i) - v * ∑ i, c i := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hb, hc, ht] at h
    linarith

/-- Rearrangement pairs two vectors at most as strongly as their respective
descending sorts, with no sign restriction. Marshall–Olkin–Arnold (2011), §6.A. -/
theorem sum_mul_le_sum_sortedVector_mul {ι : Type*} [Fintype ι]
    (a x : ι → ℝ) : (∑ i, a i * x i) ≤ ∑ i, sortedVector a i * sortedVector x i := by
  let σ : Equiv.Perm (Fin (Fintype.card ι)) := (sortingEquiv a).trans (sortingEquiv x).symm
  have h := ((sortedVector_antitone a).monovary (sortedVector_antitone x)).sum_smul_comp_perm_le_sum_smul
    (σ := σ)
  simp only [smul_eq_mul] at h
  have he : (∑ i, sortedVector a i * sortedVector x (σ i)) = ∑ i, a i * x i := by
    simp only [sortedVector, Function.comp_apply, σ, Equiv.trans_apply,
      Equiv.apply_symm_apply]
    exact (sortingEquiv a).sum_comp (fun i => a i * x i)
  rwa [he] at h

/-- Majorization bounds every sorted-weight support functional.
Marshall–Olkin–Arnold (2011), the linear support criterion for HLP. -/
theorem Majorized.sum_sortedVector_mul_le {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} (hxy : Majorized x y) (a : ι → ℝ) :
    (∑ i, sortedVector a i * sortedVector x i) ≤
      ∑ i, sortedVector a i * sortedVector y i := by
  apply sum_mul_le_of_prefix_le_of_sum_eq _ _ _ (sortedVector_antitone a)
  · exact hxy.1
  · change (∑ i, id (sortedVector x i)) = ∑ i, id (sortedVector y i)
    rw [sum_sortedVector x id, sum_sortedVector y id]
    exact hxy.2

/-- For any real weights, a majorized vector has a pairing bounded by an actual
permutation of the comparator. This is the exact support bound used in HLP.
Marshall–Olkin–Arnold (2011), Theorem 2.B.2. -/
theorem Majorized.exists_perm_sum_mul_le {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} (hxy : Majorized x y) (a : ι → ℝ) :
    ∃ σ : Equiv.Perm ι, (∑ i, a i * x i) ≤ ∑ i, a i * y (σ i) := by
  let σ : Equiv.Perm ι := (sortingEquiv a).symm.trans (sortingEquiv y)
  refine ⟨σ, ?_⟩
  calc
    (∑ i, a i * x i) ≤ ∑ i, sortedVector a i * sortedVector x i :=
      sum_mul_le_sum_sortedVector_mul a x
    _ ≤ ∑ i, sortedVector a i * sortedVector y i := hxy.sum_sortedVector_mul_le a
    _ = ∑ i, a i * y (σ i) := by
      rw [← (sortingEquiv a).sum_comp (fun i => a i * y (σ i))]
      simp [sortedVector, σ]

end NLAlib

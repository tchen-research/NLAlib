import NLAlib.ForMathlib.Combinatorics.SubsetInsertionCount
import NLAlib.ForMathlib.Combinatorics.OrderedSubsetSums
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Nonnegative elementary-symmetric sums and ordered tails

Pure finite counting bounds used by determinant-weighted pivoting. No ordering of the
values is required: the tails refer only to the given finite labels. Every zero-degree
and zero-tail endpoint is retained without division. Source: Epperly (2026), §2,
with the explicit injection/counting route in the audited library derivation.
-/

noncomputable section
open scoped BigOperators
namespace NLAlib

/-- Expanding a power counts every distinct-index q-subset q! times; all remaining
monomials are nonnegative. Includes q=0, empty sets, and q above the cardinality. -/
theorem factorial_mul_sum_powersetCard_prod_le_sum_pow {α : Type*}
    [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (q : ℕ) :
    (q.factorial : ℝ) * (∑ S ∈ s.powersetCard q, ∏ i ∈ S, f i) ≤
      (∑ i ∈ s, f i) ^ q := by
  classical
  let F : (Fin q → α) → ℝ := fun h => if Function.Injective h then
    if Finset.univ.image h ⊆ s then ∏ i ∈ Finset.univ.image h, f i else 0 else 0
  have hFilter : (((Finset.univ : Finset α).powersetCard q).filter (· ⊆ s)) =
      s.powersetCard q := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact and_comm
  have hRestrict : (∑ S ∈ (Finset.univ : Finset α).powersetCard q,
      if S ⊆ s then ∏ i ∈ S, f i else 0) = ∑ S ∈ s.powersetCard q, ∏ i ∈ S, f i := by
    rw [← Finset.sum_filter, hFilter]
  have hCount : (q.factorial : ℝ) * (∑ S ∈ s.powersetCard q, ∏ i ∈ S, f i) =
      ∑ h : Fin q → α, F h := by
    simpa only [F, hRestrict, nsmul_eq_mul] using
      (Finset.sum_injective_image_eq_factorial_nsmul
        (fun S => if S ⊆ s then ∏ i ∈ S, f i else (0 : ℝ)) q).symm
  let H := Fintype.piFinset (fun _ : Fin q => s)
  have hSmall : (∑ h : Fin q → α, F h) = ∑ h ∈ H, F h := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro h _ hh
    have hNotSub : ¬ Finset.univ.image h ⊆ s := by
      intro hSub
      apply hh
      apply Fintype.mem_piFinset.mpr
      intro j
      apply hSub
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simp [F, hNotSub]
  rw [hCount, hSmall, Finset.sum_pow']
  apply Finset.sum_le_sum
  intro h hh
  have hRange : ∀ j, h j ∈ s := Fintype.mem_piFinset.mp hh
  have hSub : Finset.univ.image h ⊆ s := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hRange j
  by_cases hInj : Function.Injective h
  · simp only [F, if_pos hInj, if_pos hSub]
    rw [Finset.prod_image hInj.injOn]
  · simp only [F, if_neg hInj]
    exact Finset.prod_nonneg (fun j _ => hf _ (hRange j))

/-- Repeated insertion bounds the r-th elementary sum by the product of the first r
label-tail sums. The sequence need not be sorted. -/
theorem sum_powersetCard_prod_le_prod_sum_tail {n : ℕ} (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) (r : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i) ≤
      ∏ j : Fin r, ∑ i : Fin n, if (j : ℕ) ≤ (i : ℕ) then f i else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ht : 0 ≤ ∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hf i
      · exact le_rfl
    calc
      _ ≤ (∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0) *
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i :=
        sum_powersetCard_prod_succ_le_tail_mul_sum_prod f hf r
      _ ≤ (∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0) *
          ∏ j : Fin r, ∑ i : Fin n, if (j : ℕ) ≤ (i : ℕ) then f i else 0 :=
        mul_le_mul_of_nonneg_left ih ht
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; exact mul_comm _ _

private theorem card_filter_fin_val_lt_le {n : ℕ} (S : Finset (Fin n)) (r : ℕ) :
    (S.filter (fun i : Fin n => (i : ℕ) < r)).card ≤ r := by
  have hsub : (S.filter (fun i : Fin n => (i : ℕ) < r)).image Fin.val ⊆ Finset.range r := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hc
  exact hc

/-- Inject a k-subset into an r-subset and a (k-r)-subset of the label tail after r.
The first part is chosen to contain all selected labels below r; the original subset
is recovered by union. Every monomial is retained exactly once in the injection. -/
theorem sum_powersetCard_prod_le_mul_sum_powersetCard_tail {n r k : ℕ}
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (hrk : r ≤ k) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, f i) ≤
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i) *
        ∑ T ∈ ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => r ≤ (i : ℕ))).powersetCard (k - r),
          ∏ i ∈ T, f i := by
  classical
  let K := (Finset.univ : Finset (Fin n)).powersetCard k
  let Tail := (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => r ≤ (i : ℕ))
  let P := ((Finset.univ : Finset (Fin n)).powersetCard r) ×ˢ Tail.powersetCard (k - r)
  have hExists (S : Finset (Fin n)) (hS : S ∈ K) :
      ∃ H : Finset (Fin n), (S.filter (fun i : Fin n => (i : ℕ) < r)) ⊆ H ∧ H ⊆ S ∧ H.card = r := by
    exact Finset.exists_subsuperset_card_eq (Finset.filter_subset _ _)
      (card_filter_fin_val_lt_le S r) (by rw [(Finset.mem_powersetCard.mp hS).2]; exact hrk)
  let head (S : Finset (Fin n)) := if hS : S ∈ K then Classical.choose (hExists S hS) else ∅
  have hHead (S : Finset (Fin n)) (hS : S ∈ K) :
      (S.filter (fun i : Fin n => (i : ℕ) < r)) ⊆ head S ∧ head S ⊆ S ∧ (head S).card = r := by
    dsimp only [head]
    rw [dif_pos hS]
    exact Classical.choose_spec (hExists S hS)
  let g (S : Finset (Fin n)) := (head S, S \ head S)
  have hg (S : Finset (Fin n)) (hS : S ∈ K) : g S ∈ P := by
    have hH := hHead S hS
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hH.2.2⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro i hi
        have hiS := (Finset.mem_sdiff.mp hi).1
        have hiH := (Finset.mem_sdiff.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hn
        exact hiH (hH.1 (Finset.mem_filter.mpr ⟨hiS, by omega⟩))
      · rw [Finset.card_sdiff_of_subset hH.2.1, (Finset.mem_powersetCard.mp hS).2, hH.2.2]
  have hInj : ∀ S ∈ K, ∀ T ∈ K, g S = g T → S = T := by
    intro S hS T hT he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    calc
      S = head S ∪ (S \ head S) := (Finset.union_sdiff_of_subset (hHead S hS).2.1).symm
      _ = head T ∪ (T \ head T) := congrArg₂ (· ∪ ·) h₁ h₂
      _ = T := Finset.union_sdiff_of_subset (hHead T hT).2.1
  have hWeight (S : Finset (Fin n)) (hS : S ∈ K) :
      (∏ i ∈ (g S).1, f i) * (∏ i ∈ (g S).2, f i) = ∏ i ∈ S, f i := by
    simpa only [g, mul_comm] using Finset.prod_sdiff (f := f) (hHead S hS).2.1
  have hImage : (∑ S ∈ K, ∏ i ∈ S, f i) =
      ∑ z ∈ K.image g, (∏ i ∈ z.1, f i) * ∏ i ∈ z.2, f i := by
    rw [Finset.sum_image hInj]
    exact Finset.sum_congr rfl (fun S hS => (hWeight S hS).symm)
  have hLe : (∑ S ∈ K, ∏ i ∈ S, f i) ≤
      ∑ z ∈ P, (∏ i ∈ z.1, f i) * ∏ i ∈ z.2, f i := by
    rw [hImage]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
      exact hg S hS
    · intro z _ _
      exact mul_nonneg (Finset.prod_nonneg (fun i _ => hf i))
        (Finset.prod_nonneg (fun i _ => hf i))
  convert hLe using 1
  dsimp only [P, Tail]
  rw [Finset.sum_product]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- The factorial elementary-symmetric bound needed for the actual pivot-history tail:
(k-r)! e_k ≤ (product of the first r label tails) times the (k-r)-th power of tail r.
All factors are retained, so zero tails and r=k need no positivity or cancellation. -/
theorem factorial_mul_sum_powersetCard_prod_le_prod_sum_tail_mul_pow {n r k : ℕ}
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (hrk : r ≤ k) :
    ((k - r).factorial : ℝ) *
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, f i) ≤
      (∏ j : Fin r, ∑ i : Fin n, if (j : ℕ) ≤ (i : ℕ) then f i else 0) *
        (∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0) ^ (k - r) := by
  let T := (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => r ≤ (i : ℕ))
  have hSplit := sum_powersetCard_prod_le_mul_sum_powersetCard_tail f hf hrk
  have hHead := sum_powersetCard_prod_le_prod_sum_tail f hf r
  have hFac := factorial_mul_sum_powersetCard_prod_le_sum_pow T f (fun i _ => hf i) (k - r)
  have hSum : (∑ i ∈ T, f i) = ∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0 := by
    simp only [T, Finset.sum_filter]
  rw [hSum] at hFac
  have hE : 0 ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i :=
    Finset.sum_nonneg (fun S _ => Finset.prod_nonneg (fun i _ => hf i))
  have hTail : 0 ≤ ∑ i : Fin n, if r ≤ (i : ℕ) then f i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hf i
    · exact le_rfl
  calc
    _ ≤ ((k - r).factorial : ℝ) *
        ((∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i) *
          ∑ S ∈ T.powersetCard (k - r), ∏ i ∈ S, f i) :=
      mul_le_mul_of_nonneg_left hSplit (Nat.cast_nonneg _)
    _ = (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, f i) *
        (((k - r).factorial : ℝ) * ∑ S ∈ T.powersetCard (k - r), ∏ i ∈ S, f i) := by
      rw [mul_left_comm]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hFac hE).trans
      (mul_le_mul_of_nonneg_right hHead (pow_nonneg hTail _))

end NLAlib

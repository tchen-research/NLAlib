import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite subset counting for volume sampling

Adding an outside index to a size-`k` subset counts every size-`k+1` subset exactly
`k+1` times. This is the exact finite expectation count of manuscript `sa:volume-theorem`.
-/

noncomputable section
namespace NLAlib

/-- Summing an insertion weight over all size-`k` sets and all outside indices counts
each size-`k+1` set exactly `k+1` times. Source: manuscript `sa:volume-theorem`;
Deshpande--Rademacher--Vempala--Wang (2006), exact volume-sampling error. -/
theorem sum_powersetCard_sum_insert_eq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (w : Finset ι → ℝ) :
    (∑ S ∈ s.powersetCard k, ∑ i ∈ s, if i ∉ S then w (insert i S) else 0) =
      (k + 1 : ℝ) * ∑ T ∈ s.powersetCard (k + 1), w T := by
  let P := ((s.powersetCard k) ×ˢ s).filter fun x => x.2 ∉ x.1
  let T := ((s.powersetCard (k + 1)) ×ˢ s).filter fun x => x.2 ∈ x.1
  have hbij : (∑ x ∈ P, w (insert x.2 x.1)) = ∑ x ∈ T, w x.1 := by
    apply Finset.sum_nbij' (fun x => (insert x.2 x.1, x.2))
      (fun x => (x.1.erase x.2, x.2))
    · rintro ⟨S, i⟩ h
      rcases (by simpa only [P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_powersetCard] using h) with ⟨⟨⟨hSs, hCard⟩, his⟩, hiS⟩
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
      exact ⟨⟨⟨Finset.insert_subset his hSs, by
        rw [Finset.card_insert_of_notMem hiS, hCard]⟩, his⟩, Finset.mem_insert_self _ _⟩
    · rintro ⟨S, i⟩ h
      rcases (by simpa only [T, Finset.mem_filter, Finset.mem_product,
        Finset.mem_powersetCard] using h) with ⟨⟨⟨hSs, hCard⟩, his⟩, hiS⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
      exact ⟨⟨⟨(Finset.erase_subset _ _).trans hSs, by
        rw [Finset.card_erase_of_mem hiS, hCard]; omega⟩, his⟩, Finset.notMem_erase _ _⟩
    · rintro ⟨S, i⟩ h
      have hiS : i ∉ S := (Finset.mem_filter.mp h).2
      simp only [Finset.erase_insert hiS]
    · rintro ⟨S, i⟩ h
      have hiS : i ∈ S := (Finset.mem_filter.mp h).2
      simp only [Finset.insert_erase hiS]
    · intros
      rfl
  have hcount : (∑ S ∈ s.powersetCard k, ∑ i ∈ s,
      if i ∉ S then w (insert i S) else 0) =
      ∑ S ∈ s.powersetCard (k + 1), ∑ i ∈ s, if i ∈ S then w S else 0 := by
    simpa only [P, T, Finset.sum_filter, Finset.sum_product] using hbij
  rw [hcount, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rcases Finset.mem_powersetCard.mp hS with ⟨hSs, hCard⟩
  calc (∑ i ∈ s, if i ∈ S then w S else 0) = ∑ i ∈ S, if i ∈ S then w S else 0 :=
      (Finset.sum_subset hSs (fun i _ hi => by simp only [if_neg hi])).symm
    _ = (k + 1 : ℝ) * w S := by
      simp [hCard]

/-- Every size-`k+1` subset of zero-indexed finite labels contains a label at least
`k`. Source: manuscript `sa:volume-theorem`, the finite tail-index argument. -/
theorem exists_tail_mem_of_mem_powersetCard_succ {n k : ℕ} {T : Finset (Fin n)}
    (hT : T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1)) :
    ∃ i ∈ T, k ≤ (i : ℕ) := by
  let H := (Finset.univ : Finset (Fin n)).filter fun i : Fin n => (i : ℕ) < k
  have hH : H.card ≤ k := by
    have hi : H.image Fin.val ⊆ Finset.range k := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    calc H.card = (H.image Fin.val).card := (Finset.card_image_of_injective H Fin.val_injective).symm
      _ ≤ (Finset.range k).card := Finset.card_le_card hi
      _ = k := Finset.card_range k
  by_contra h
  push Not at h
  have hsub : T ⊆ H := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i hi⟩
  have hc := (Finset.card_le_card hsub).trans hH
  rw [(Finset.mem_powersetCard.mp hT).2] at hc
  omega

/-- A nonnegative elementary spectral sum is dominated by the previous elementary
sum times the zero-indexed spectral tail. Source: manuscript `sa:volume-theorem`;
Deshpande et al. (2006), the factor-`k+1` upper bound. No strict eigenvalue positivity
or ordering is needed for this finite subset inequality. -/
theorem sum_powersetCard_prod_succ_le_tail_mul_sum_prod {n : ℕ}
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (k : ℕ) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1), ∏ i ∈ T, d i) ≤
      (∑ i : Fin n, if k ≤ (i : ℕ) then d i else 0) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, d i := by
  classical
  cases n with
  | zero =>
    have he : (∅ : Finset (Fin 0)).powersetCard (k + 1) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    simp [he]
  | succ n =>
    let K := (Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1)
    let H := (Finset.univ : Finset (Fin (n + 1))).filter fun i : Fin (n + 1) => k ≤ (i : ℕ)
    let P := H ×ˢ ((Finset.univ : Finset (Fin (n + 1))).powersetCard k)
    let chosen (T : Finset (Fin (n + 1))) : Fin (n + 1) :=
      if hT : T ∈ K then Classical.choose (exists_tail_mem_of_mem_powersetCard_succ hT) else 0
    have hchosen : ∀ T ∈ K, chosen T ∈ T ∧ k ≤ (chosen T : ℕ) := by
      intro T hT
      dsimp only [chosen]
      rw [dif_pos hT]
      exact Classical.choose_spec (exists_tail_mem_of_mem_powersetCard_succ hT)
    let f (T : Finset (Fin (n + 1))) := (chosen T, T.erase (chosen T))
    have hf : ∀ T ∈ K, f T ∈ P := by
      intro T hT
      obtain ⟨hi, htail⟩ := hchosen T hT
      simp only [P, f, Finset.mem_product, H, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      refine ⟨htail, ?_⟩
      rw [Finset.card_erase_of_mem hi, (Finset.mem_powersetCard.mp hT).2]
      omega
    have hinj : ∀ T ∈ K, ∀ S ∈ K, f T = f S → T = S := by
      intro T hT S hS he
      have hi : chosen T = chosen S := congrArg Prod.fst he
      have he' : T.erase (chosen T) = S.erase (chosen S) := congrArg Prod.snd he
      calc T = insert (chosen T) (T.erase (chosen T)) := (Finset.insert_erase (hchosen T hT).1).symm
        _ = insert (chosen S) (S.erase (chosen S)) := congrArg₂ (fun i S => insert i S) hi he'
        _ = S := Finset.insert_erase (hchosen S hS).1
    have hprod : ∀ T ∈ K, d (f T).1 * (∏ i ∈ (f T).2, d i) = ∏ i ∈ T, d i := by
      intro T hT
      exact Finset.mul_prod_erase T d (hchosen T hT).1
    have himage : (∑ T ∈ K, ∏ i ∈ T, d i) =
        ∑ z ∈ K.image f, d z.1 * ∏ i ∈ z.2, d i := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun T hT => (hprod T hT).symm
    have hle : (∑ T ∈ K, ∏ i ∈ T, d i) ≤ ∑ z ∈ P, d z.1 * ∏ i ∈ z.2, d i := by
      rw [himage]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨T, hT, rfl⟩
        exact hf T hT
      · intro z _ _
        exact mul_nonneg (hd z.1) (Finset.prod_nonneg fun i _ => hd i)
    convert hle using 1
    dsimp only [P]
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [H, Finset.sum_filter]

end NLAlib

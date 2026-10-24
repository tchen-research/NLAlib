/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Module

/-!
# Counting ordered enumerations of fixed-size subsets

A size-`k` subset has exactly `k!` injective enumerations by `Fin k`.
The corresponding weighted sum identity also includes `k=0` and `k` larger
than the ambient cardinality.
-/

noncomputable section
open scoped BigOperators

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

private def injectiveImageEquiv (S : Finset α) :
    {h : Fin k → α // Function.Injective h ∧ univ.image h = S} ≃ (Fin k ≃ S) where
  toFun h := Equiv.ofBijective (fun i =>
    ⟨h.1 i, by
      have hi : h.1 i ∈ univ.image h.1 := mem_image.mpr ⟨i, mem_univ _, rfl⟩
      exact Eq.mp (congrArg (fun T : Finset α => h.1 i ∈ T) h.2.2) hi⟩) (by
      constructor
      · intro i j hij
        exact h.2.1 (congrArg Subtype.val hij)
      · intro x
        have hx : x.1 ∈ univ.image h.1 :=
          Eq.mp (congrArg (fun T : Finset α => x.1 ∈ T) h.2.2.symm) x.2
        obtain ⟨i, _, hi⟩ := mem_image.mp hx
        exact ⟨i, Subtype.ext hi⟩)
  invFun e := ⟨fun i => (e i).1, (Subtype.val_injective.comp e.injective), by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact (e i).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact mem_image.mpr ⟨i, mem_univ _, congrArg Subtype.val hi⟩⟩
  left_inv h := by apply Subtype.ext; funext i; rfl
  right_inv e := by ext i; rfl

/-- There are `k!` injective functions with a specified size-`k` image. -/
theorem card_injective_functions_image (S : Finset α) (hS : S.card = k) :
    (((univ : Finset (Fin k → α)).filter Function.Injective).filter
      (fun h => univ.image h = S)).card = k.factorial := by
  classical
  let D := ((univ : Finset (Fin k → α)).filter Function.Injective).filter
    (fun h => univ.image h = S)
  have e : D ≃ {h : Fin k → α // Function.Injective h ∧ univ.image h = S} :=
    Equiv.subtypeEquivRight fun _ => by simp [D]
  rw [← Fintype.card_coe D, Fintype.card_congr e,
    Fintype.card_congr (injectiveImageEquiv S),
    Fintype.card_equiv (S.equivFinOfCardEq hS).symm, Fintype.card_fin]

/-- Summing a support-dependent weight over injective ordered histories counts
each size-`k` subset exactly `k!` times. No order on the ambient type is required. -/
theorem sum_injective_image_eq_factorial_nsmul {M : Type*} [AddCommMonoid M]
    (f : Finset α → M) (k : ℕ) :
    (∑ h : Fin k → α, if Function.Injective h then f (univ.image h) else 0) =
      k.factorial • ∑ S ∈ (univ : Finset α).powersetCard k, f S := by
  classical
  rw [← sum_filter]
  have hMap : ∀ h ∈ ((univ : Finset (Fin k → α)).filter Function.Injective),
      univ.image h ∈ (univ : Finset α).powersetCard k := by
    intro h hh
    rw [mem_powersetCard]
    exact ⟨subset_univ _, by rw [card_image_of_injective _ (mem_filter.mp hh).2, card_univ,
      Fintype.card_fin]⟩
  rw [← sum_fiberwise_of_maps_to' hMap f, ← sum_nsmul]
  apply sum_congr rfl
  intro S hS
  rw [sum_const, card_injective_functions_image S (mem_powersetCard.mp hS).2]

omit [DecidableEq α] in
/-- Elementary symmetric subset sums are invariant under a relabeling of the
finite ambient type. -/
theorem sum_powersetCard_prod_equiv {β R : Type*} [Fintype β] [DecidableEq β]
    [CommSemiring R] (e : α ≃ β) (f : β → R) (k : ℕ) :
    (∑ S ∈ (univ : Finset α).powersetCard k, ∏ i ∈ S, f (e i)) =
      ∑ S ∈ (univ : Finset β).powersetCard k, ∏ i ∈ S, f i := by
  rw [← map_univ_equiv e, powersetCard_map, sum_map]
  simp [mapEmbedding, prod_map]

end Finset

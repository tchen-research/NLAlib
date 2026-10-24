import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Module

/-! # Summing weights over all supersets of a fixed size

A weight attached to a small subset occurs the same number of times in the
sum over larger subsets. This finite counting identity is independent of
the determinant applications that use it.
-/

namespace Finset

open scoped BigOperators

/-- Summing the weights of the `d`-subsets inside every `s`-subset counts
each weight `choose (|T| - d) (s - d)` times. -/
theorem sum_powersetCard_sum_subset {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (T : Finset α) (d s : ℕ) (hds : d ≤ s)
    (w : Finset α → M) :
    (∑ S ∈ T.powersetCard s, ∑ J ∈ T.powersetCard d,
      if J ⊆ S then w J else 0) =
      (T.card - d).choose (s - d) • ∑ J ∈ T.powersetCard d, w J := by
  classical
  rw [Finset.sum_comm, ← Finset.sum_nsmul]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← Finset.sum_filter, Finset.sum_const,
    Finset.card_filter_powersetCard_subset J T s
      (Finset.mem_powersetCard.mp hJ).1]
  · rw [(Finset.mem_powersetCard.mp hJ).2]
  · rw [(Finset.mem_powersetCard.mp hJ).2]
    exact hds

/-- A fixed size-`s` subset occurs in exactly `choose (|T|-s) (t-s)`
size-`t` supersets inside `T`. A malformed fixed subset contributes zero. -/
theorem sum_powersetCard_ite_mem {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (T S : Finset α) (s t : ℕ) (hst : s ≤ t) (v : M) :
    (∑ R ∈ T.powersetCard t, if S ∈ R.powersetCard s then v else 0) =
      if S ∈ T.powersetCard s then (T.card - s).choose (t - s) • v else 0 := by
  classical
  by_cases hS : S ∈ T.powersetCard s
  · rw [if_pos hS]
    have hSc := (Finset.mem_powersetCard.mp hS).2
    simp only [Finset.mem_powersetCard, hSc, and_true]
    rw [← Finset.sum_filter, Finset.sum_const,
      Finset.card_filter_powersetCard_subset S T t (Finset.mem_powersetCard.mp hS).1
        (by simpa only [hSc] using hst), hSc]
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro R hR
    rw [if_neg]
    intro hSR
    exact hS (Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hSR).1.trans (Finset.mem_powersetCard.mp hR).1,
        (Finset.mem_powersetCard.mp hSR).2⟩)

end Finset

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Swapping the indices of an off-diagonal double sum

`∑ a ∈ s, ∑ c ∈ s.erase a, f a c = ∑ c ∈ s, ∑ a ∈ s.erase c, f a c`: the ordered pairs of
distinct elements of `s` are the same set whichever index is summed first
(`sum_sum_erase_comm`). With `s = univ` this swaps the two indices of an off-diagonal sum.

Source: ported from `SparseFockFormal` (`DirectionalConcrete.sum_erase_comm`,
`DirectionalConcrete.sum_ordered_swap`, `SparseIIDTransfer.sum_offDiagonal_swap`), commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

set_option autoImplicit false
open scoped BigOperators
namespace NLAlib

/-- Summing over ordered pairs of distinct elements of `s`, either index may be summed first.

Source: ported from `SparseFockFormal.DirectionalConcrete.sum_erase_comm` (generalised from `ℝ`
to an additive commutative monoid), b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports
`sparse-ose`. -/
theorem sum_sum_erase_comm {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → M) :
    (∑ a ∈ s, ∑ c ∈ s.erase a, f a c) = ∑ c ∈ s, ∑ a ∈ s.erase c, f a c := by
  have hexpand (g : α → α → M) :
      (∑ a ∈ s, ∑ c ∈ s.erase a, g a c) =
        ∑ a ∈ s, ∑ c ∈ s, if c ≠ a then g a c else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.filter_ne' s a, Finset.sum_filter]
  rw [hexpand f, hexpand (fun c a ↦ f a c), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c = a <;> simp [h, Ne.symm]

end NLAlib

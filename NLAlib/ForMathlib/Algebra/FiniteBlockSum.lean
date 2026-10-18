import Mathlib.Algebra.BigOperators.Intervals

/-! # Reindexing finite sums by consecutive equal blocks

The block decomposition is useful for comparing uniform path subdivisions
with their common refinements. It is a generic finite-sum identity.
-/

namespace Finset

/-- A sum over `n * m` consecutive indices splits into `n` consecutive blocks
of size `m`. Empty dimensions are included. -/
theorem sum_range_mul_blocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n m : ℕ) :
    ∑ k ∈ range (n * m), f k = ∑ i ∈ range n, ∑ j ∈ range m, f (i * m + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

end Finset

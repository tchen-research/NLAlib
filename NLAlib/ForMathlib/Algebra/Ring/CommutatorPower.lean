import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A finite noncommutative power commutator identity

The commutator with a power is the actual finite sum of conjugate-position
commutators. This is the discrete product rule, proved by a native telescoping
sum and valid in every unital ring.
-/

noncomputable section
set_option autoImplicit false

/-- The commutator with a power is the exact sum over its possible insertion
positions. No commutation assumption on the ring elements is used. -/
theorem mul_pow_sub_pow_mul_eq_sum {R : Type*} [Ring R] (a b : R) (n : ℕ) :
    a * b ^ n - b ^ n * a =
      ∑ k ∈ Finset.range n, b ^ k * (a * b - b * a) * b ^ (n - 1 - k) := by
  let f : ℕ → R := fun k => b ^ k * a * b ^ (n - k)
  calc
    _ = f 0 - f n := by simp [f]
    _ = ∑ k ∈ Finset.range n, (f k - f (k + 1)) := (Finset.sum_range_sub' f n).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hsub : n - k = (n - 1 - k) + 1 := by omega
      have hsub' : n - (k + 1) = n - 1 - k := by omega
      dsimp only [f]
      rw [hsub, hsub', pow_succ b k, pow_succ' b (n - 1 - k)]
      noncomm_ring

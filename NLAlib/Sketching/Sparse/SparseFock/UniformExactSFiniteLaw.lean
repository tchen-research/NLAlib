/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.ForMathlib.Probability.FiniteLaw
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Small finite-law constructions for uniform exact-s columns

The main finite-probability development deliberately contains only the
constructions needed by SparseStack.  The exact-s extension additionally uses
uniform laws on arbitrary nonempty finite types and finite pushforwards.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.FiniteLaw

noncomputable section

variable {α β : Type*}

/-- Two explicit finite laws are equal when their point masses agree.

Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ext_weight [Fintype α] {μ ν : FiniteLaw α}
    (h : μ.weight = ν.weight) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk v hv ht =>
      dsimp at h
      subst v
      rfl

/-- The uniform law on a nonempty finite type.

Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def uniform [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / (Fintype.card α : ℝ)
  weight_nonneg _ := by positivity
  sum_weight := by
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

/-- A uniform law on a nonempty finite type assigns reciprocal-cardinality mass to each point.
Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem uniform_weight [Fintype α] [Nonempty α] (x : α) :
    (uniform : FiniteLaw α).weight x = 1 / (Fintype.card α : ℝ) := rfl

/-- Push a finite law forward along an arbitrary map.

Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def map [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) : FiniteLaw β where
  weight y := ∑ x, if f x = y then μ.weight x else 0
  weight_nonneg y := Finset.sum_nonneg fun x _ => by
    by_cases h : f x = y
    · simp [h, μ.weight_nonneg x]
    · simp [h]
  sum_weight := by
    classical
    rw [Finset.sum_comm]
    simpa using μ.sum_weight

/-- A mapped finite law assigns the sum of masses over each point's preimage fiber.
Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem map_weight [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) (y : β) :
    (map μ f).weight y = ∑ x, if f x = y then μ.weight x else 0 := rfl

/-- Expectations under a pushforward are expectations after composition.

Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem map_expect [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (map μ f).expect g = μ.expect (fun x => g (f x)) := by
  classical
  simp only [FiniteLaw.expect, map_weight]
  calc
    (∑ y, (∑ x, if f x = y then μ.weight x else 0) * g y) =
        ∑ y, ∑ x, (if f x = y then μ.weight x else 0) * g y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
    _ = ∑ x, μ.weight x * g (f x) := by
      rw [Finset.sum_comm]
      simp

/-- A bijection sends a uniform finite law to a uniform finite law.

Source: ported from `SparseFockFormal.UniformExactSFiniteLaw`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem map_uniform_equiv [Fintype α] [Fintype β] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    map (uniform : FiniteLaw α) e = (uniform : FiniteLaw β) := by
  classical
  apply ext_weight
  funext y
  simp only [map_weight, uniform_weight]
  rw [show (∑ x, if e x = y then 1 / (Fintype.card α : ℝ) else 0) =
      1 / (Fintype.card α : ℝ) by
    rw [Finset.sum_eq_single (e.symm y)]
    · simp
    · intro x _ hx
      have hxy : e x ≠ y := by
        intro h
        apply hx
        exact e.injective (h.trans (e.apply_symm_apply y).symm)
      simp [hxy]
    · simp]
  rw [Fintype.card_congr e]

end

end NLAlib.SparseFock.FiniteLaw

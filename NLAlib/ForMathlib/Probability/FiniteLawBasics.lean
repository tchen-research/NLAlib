/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Elementary probability on finite types

This file supplies a small, explicit probability foundation for the finite
random objects in the sparse-Fock argument.  A `FiniteLaw α` is a nonnegative
real weight on the finite type `α` whose total mass is one.  Expectations and
event probabilities are finite sums, so none of the results below hide
measurability, integrability, or independence hypotheses.

The main construction is `FiniteLaw.independentProduct`.  Its outcome is a
function `x : ι → α`, and its mass is the literal product of the coordinate
masses.  The coordinate marginal, separated-observable factorization, and
cylinder-event factorization theorems therefore give genuine mutual
independence of the coordinates.
-/

open scoped BigOperators

namespace NLAlib.SparseFock

noncomputable section

/-- A probability law on a finite type, represented by explicit real weights.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  /-- Probability mass of an outcome.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
  weight : α → ℝ
  /-- Every outcome has nonnegative mass.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
  weight_nonneg : ∀ x, 0 ≤ weight x
  /-- The total mass is one.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
  sum_weight : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β ι κ : Type*}

section Basic

variable [Fintype α]

/-- The expectation of a real-valued observable under a finite law.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

/-- The real indicator of a set.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def indicator (s : Set α) (x : α) : ℝ :=
  by
    classical
    exact if x ∈ s then 1 else 0

/-- Probability of an event, defined as the expectation of its indicator.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def prob (μ : FiniteLaw α) (s : Set α) : ℝ :=
  μ.expect (indicator s)

/-- The finite expectation of the zero function is zero.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem expect_zero (μ : FiniteLaw α) :
    μ.expect (fun _ => 0) = 0 := by
  simp [expect]

/-- The finite expectation of one is one.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem expect_one (μ : FiniteLaw α) :
    μ.expect (fun _ => 1) = 1 := by
  simpa [expect] using μ.sum_weight

/-- The finite expectation of a constant is that constant.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  calc
    μ.expect (fun _ => c) = (∑ x, μ.weight x) * c := by
      simp_rw [expect, Finset.sum_mul]
    _ = c := by rw [μ.sum_weight, one_mul]

/-- Finite expectation preserves addition of observables.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x + g x) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

/-- Finite expectation preserves subtraction of observables.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

/-- Finite expectation preserves negation of observables.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_neg (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun x => -f x) = -μ.expect f := by
  simp [expect]

/-- A real scalar factors out of finite expectation.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_smul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- Pointwise equal observables have equal finite expectations.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_congr (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, f x = g x) : μ.expect f = μ.expect g := by
  apply Finset.sum_congr rfl
  intro x _hx
  rw [h x]

/-- A pointwise nonnegative observable has nonnegative finite expectation.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg fun x _hx => mul_nonneg (μ.weight_nonneg x) (hf x)

/-- Finite expectation preserves pointwise order.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_of_nonneg_left (hfg x) (μ.weight_nonneg x)

/-- The absolute finite expectation is at most the finite expectation of the absolute value.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem abs_expect_le_expect_abs (μ : FiniteLaw α) (f : α → ℝ) :
    |μ.expect f| ≤ μ.expect (fun x => |f x|) := by
  calc
    |μ.expect f| = |∑ x, μ.weight x * f x| := rfl
    _ ≤ ∑ x, |μ.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.expect (fun x => |f x|) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [abs_mul, abs_of_nonneg (μ.weight_nonneg x)]

/-- The empty event has probability zero.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem prob_empty (μ : FiniteLaw α) : μ.prob ∅ = 0 := by
  classical
  calc
    μ.prob ∅ = μ.expect (fun _ => 0) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      unfold indicator
      simp
    _ = 0 := μ.expect_zero

/-- The whole finite outcome space has probability one.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem prob_univ (μ : FiniteLaw α) : μ.prob Set.univ = 1 := by
  classical
  calc
    μ.prob Set.univ = μ.expect (fun _ => 1) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      unfold indicator
      simp
    _ = 1 := μ.expect_one

/-- Every finite-law event probability is nonnegative.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_nonneg (μ : FiniteLaw α) (s : Set α) : 0 ≤ μ.prob s := by
  classical
  apply μ.expect_nonneg
  intro x
  unfold indicator
  split <;> norm_num

/-- Every finite-law event probability is at most one.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_le_one (μ : FiniteLaw α) (s : Set α) : μ.prob s ≤ 1 := by
  classical
  calc
    μ.prob s ≤ μ.expect (fun _ => 1) := by
      apply μ.expect_mono
      intro x
      unfold indicator
      split <;> norm_num
    _ = 1 := μ.expect_one

/-- Every finite-law event probability belongs to the closed unit interval.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_mem_Icc (μ : FiniteLaw α) (s : Set α) : μ.prob s ∈ Set.Icc 0 1 :=
  ⟨μ.prob_nonneg s, μ.prob_le_one s⟩

/-- Finite-law probability is monotone under event inclusion.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_mono (μ : FiniteLaw α) {s t : Set α} (hst : s ⊆ t) :
    μ.prob s ≤ μ.prob t := by
  classical
  apply μ.expect_mono
  intro x
  by_cases hx : x ∈ s
  · have hxt : x ∈ t := hst hx
    simp [indicator, hx, hxt]
  · unfold indicator
    simp only [hx, ↓reduceIte]
    split <;> norm_num

/-- The probability of the complementary event is one minus the original probability.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_compl (μ : FiniteLaw α) (s : Set α) :
    μ.prob sᶜ = 1 - μ.prob s := by
  classical
  calc
    μ.prob sᶜ = μ.expect (fun x => 1 - indicator s x) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      by_cases hx : x ∈ s <;> simp [indicator, hx]
    _ = μ.expect (fun _ => 1) - μ.expect (indicator s) := μ.expect_sub _ _
    _ = 1 - μ.prob s := by rw [μ.expect_one]; rfl

/-- The probability of a singleton is its assigned weight.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem prob_singleton [DecidableEq α] (μ : FiniteLaw α) (a : α) :
    μ.prob {a} = μ.weight a := by
  classical
  simp [prob, expect, indicator]

/-- Finite Markov inequality in multiplication form.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem markov_mul (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (threshold : ℝ) :
    threshold * μ.prob {x | threshold ≤ f x} ≤ μ.expect f := by
  classical
  rw [prob, expect, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hlarge : threshold ≤ f x
  · simp [indicator, hlarge]
    calc
      threshold * μ.weight x = μ.weight x * threshold := by ring
      _ ≤ μ.weight x * f x :=
        mul_le_mul_of_nonneg_left hlarge (μ.weight_nonneg x)
  · simp [indicator, hlarge]
    exact mul_nonneg (μ.weight_nonneg x) (hf x)

/-- Standard divided form of finite Markov's inequality.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem markov (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    μ.prob {x | threshold ≤ f x} ≤ μ.expect f / threshold := by
  apply (le_div_iff₀ hthreshold).2
  simpa [mul_comm] using μ.markov_mul hf threshold

end Basic

end FiniteLaw

end

end NLAlib.SparseFock

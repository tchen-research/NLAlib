import Mathlib.Data.Fintype.Card

/-!
# Finsets of a prescribed size as a type

`ExactRowSubset α k` is the subtype of `Finset α` of cardinality exactly `k`. It is the
sample space of uniform sampling without replacement (`uniformExactRowSubsetPMF`) and the index
type of compound matrices in Cauchy–Binet (`SizedSubset k r` is `ExactRowSubset k (card r)`).
Mathlib has the finset `Finset.powersetCard k s` but no named subtype. Moved from
`NLAlib.ForMathlib.Probability.UniformSamplingCoupling` (adapted from
Rerandomized-Subsampled-Trigonometric-Transforms, MIT licence, Diar Heidary).
-/

namespace NLAlib

/-- The finite sample space of literal size-`k` subsets.
Source: operator re-derivation `sh:convex-sampling`. -/
abbrev ExactRowSubset (α : Type*) (k : ℕ) := {T : Finset α // T.card = k}

/-- Exact-size subsets exist when the requested size is at most the population.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem exactRowSubset_nonempty {α : Type*} [Fintype α] {k : ℕ}
    (hk : k ≤ Fintype.card α) : Nonempty (ExactRowSubset α k) := by
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α))
    (by simpa using hk)
  exact ⟨T, hT⟩

end NLAlib

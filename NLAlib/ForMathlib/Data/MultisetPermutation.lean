import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations of equal finite value multisets

Equality of value multisets is equality of every fiber cardinality, so
fiber equivalences combine into a permutation of the index type.
This supports eigenvalue-list transport in Horn–Johnson (2013), §2.5.
-/

noncomputable section

namespace NLAlib

/-- Equal finite indexed value multisets differ by an index permutation.
Source: the finite multiset multiplicity criterion; supports normal-matrix
unitary similarity and prescribed eigenvalue ordering. -/
theorem exists_perm_eq_of_map_univ_val_eq {n α : Type*} [Fintype n]
    (a b : n → α) (hab : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Equiv.Perm n, ∀ i, b (σ i) = a i := by
  classical
  have hcard (z : α) : Fintype.card {i : n // a i = z} = Fintype.card {i : n // b i = z} := by
    have h := congrArg (Multiset.count z) hab
    simpa only [Multiset.count_map, Fintype.card_subtype, Finset.card, Finset.filter_val,
      eq_comm] using h
  let e (z : α) : {i : n // a i = z} ≃ {i : n // b i = z} := Fintype.equivOfCardEq (hcard z)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

end NLAlib

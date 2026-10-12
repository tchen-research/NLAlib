import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Sum

/-!
# Completing a finite embedding to a sum equivalence

A prescribed list of distinct coordinates can be put first in a complete
coordinate order, with the remaining coordinates given their own finite labels.
-/

noncomputable section
namespace NLAlib

/-- Complete an embedding of finite types to an equivalence from a disjoint
sum, preserving every prescribed first-summand coordinate. The cardinality
identity supplies exactly the number of remaining coordinates. -/
theorem exists_equiv_sum_extending_embedding {p q n : Type*}
    [Fintype p] [Fintype q] [Fintype n] (e : p ↪ n)
    (hcard : Fintype.card p + Fintype.card q = Fintype.card n) :
    ∃ f : (p ⊕ q) ≃ n, ∀ i, f (Sum.inl i) = e i := by
  classical
  let eL : p ≃ {j : n // j ∈ Set.range e} := Equiv.ofInjective e e.injective
  have hRange : Fintype.card {j : n // j ∈ Set.range e} = Fintype.card p :=
    Fintype.card_congr eL.symm
  have hRest : Fintype.card {j : n // j ∉ Set.range e} = Fintype.card q := by
    rw [Fintype.card_subtype_compl, hRange]
    omega
  let eR : q ≃ {j : n // j ∉ Set.range e} := Fintype.equivOfCardEq hRest.symm
  exact ⟨(Equiv.sumCongr eL eR).trans (Equiv.sumCompl (fun j => j ∈ Set.range e)),
    fun _ => rfl⟩

end NLAlib

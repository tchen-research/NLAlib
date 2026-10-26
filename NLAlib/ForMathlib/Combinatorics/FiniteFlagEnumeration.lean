import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin

/-!
# Simultaneous prefix enumeration of a finite flag

A nested finite family of finite sets can be ordered so that every member is
an initial segment of one enumeration. Elements are ordered by the number of
sets they have not yet entered; an arbitrary finite enumeration breaks ties.
-/

noncomputable section
set_option autoImplicit false

namespace Finset

private theorem mem_iff_val_lt_card_of_lower {N : ℕ} (T : Finset (Fin N))
    (hT : ∀ i ∈ T, ∀ j ≤ i, j ∈ T) (i : Fin N) :
    i ∈ T ↔ i.val < T.card := by
  constructor
  · intro hi
    have hs : Iic i ⊆ T := fun j hj => hT i hi j (mem_Iic.mp hj)
    have hc := card_le_card hs
    simp only [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hn
    have hs : T ⊆ Iio i := by
      intro j hj
      apply mem_Iio.mpr
      by_contra hji
      exact hn (hT j hj i (le_of_not_gt hji))
    have hc := card_le_card hs
    simp only [Fin.card_Iio] at hc
    omega

/-- A finite monotone flag admits one enumeration making every member an
initial segment of exactly its cardinality. Repeated sets, empty sets,
incomplete flags, and empty ambient types are all included. -/
theorem exists_equiv_fin_prefix_of_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (S : Fin (m + 1) → Finset ι) (hS : Monotone S) :
    ∃ e : Fin (Fintype.card ι) ≃ ι,
      ∀ (k : Fin (m + 1)) (i : Fin (Fintype.card ι)),
        e i ∈ S k ↔ i.val < (S k).card := by
  classical
  let excluded (x : ι) : Finset (Fin (m + 1)) := univ.filter fun k => x ∉ S k
  have hrank {x y : ι} {k : Fin (m + 1)} (hx : x ∈ S k) (hy : y ∉ S k) :
      (excluded x).card < (excluded y).card := by
    have hs : excluded x ⊆ excluded y := by
      intro j hj
      have hxj : x ∉ S j := (mem_filter.mp hj).2
      have hjk : j ≤ k := by
        by_contra hn
        exact hxj (hS (le_of_lt (lt_of_not_ge hn)) hx)
      exact mem_filter.mpr ⟨mem_univ _, fun hyj => hy (hS hjk hyj)⟩
    apply card_lt_card
    exact (ssubset_iff_of_subset hs).mpr
      ⟨k, mem_filter.mpr ⟨mem_univ _, hy⟩, by simpa [excluded] using hx⟩
  let key (x : ι) : ℕ ×ₗ Fin (Fintype.card ι) :=
    toLex ((excluded x).card, Fintype.equivFin ι x)
  have hkey : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin ι).injective
    exact congrArg (fun z : ℕ ×ₗ Fin (Fintype.card ι) => (ofLex z).2) hxy
  let : LinearOrder ι := LinearOrder.lift' key hkey
  have hlower (k : Fin (m + 1)) {x y : ι} (hxy : x ≤ y) (hy : y ∈ S k) : x ∈ S k := by
    by_contra hx
    have hr := hrank hy hx
    change key x ≤ key y at hxy
    rcases Prod.Lex.toLex_le_toLex.mp hxy with hlt | ⟨heq, _⟩ <;> omega
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  refine ⟨e.toEquiv, fun k i => ?_⟩
  let T : Finset (Fin (Fintype.card ι)) := (S k).map e.symm.toEquiv.toEmbedding
  have hmem (j : Fin (Fintype.card ι)) : j ∈ T ↔ e j ∈ S k := by
    simp [T]
  have hT : ∀ j ∈ T, ∀ l ≤ j, l ∈ T := by
    intro j hj l hlj
    exact (hmem l).mpr (hlower k (e.monotone hlj) ((hmem j).mp hj))
  have h := mem_iff_val_lt_card_of_lower T hT i
  change e i ∈ S k ↔ i.val < (S k).card
  simpa only [hmem, T, card_map] using h

end Finset

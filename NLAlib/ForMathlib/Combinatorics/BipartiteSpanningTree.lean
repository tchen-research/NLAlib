import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import NLAlib.ForMathlib.Combinatorics.BipartiteTreeSum

/-!
# Spanning-tree syntax for connected bipartite multigraphs

This file proves the bridge between an arbitrary connected bipartite multigraph
(vertex sets `U` of rows and `V` of columns with indexed edge occurrences
`sr : E -> U`, `tg : E -> V`) and the syntax `RowRootedBipartiteTree r q`
of `NLAlib.ForMathlib.Combinatorics.BipartiteTreeSum`.

The graph is encoded as `SimpleGraph.bipartiteOccurrenceGraph sr tg` on `Sum U V`:
two vertices of opposite sides are adjacent iff some occurrence has exactly those
endpoints.  **Parallel occurrences are allowed** and are handled by the final
embedding `occ : Fin t.edgeList.length ↪ E`: distinct tree edges are realized by
distinct occurrence indices (the injectivity is forced by the endpoint maps, as
the edge list of a syntax tree has no repeated edge).

## Proof strategy (maximal partial attachment)

* `Good sr tg k`: there is a tree `t : RowRootedBipartiteTree r q` with
  `k = r + 1 + q`, injective row/column maps `f`, `g` into `U`, `V`, and every
  syntax edge `(i,j)` is realized by some occurrence `e` with `sr e = f i`,
  `tg e = g j`.
* `Good sr tg 1` holds from any root row (the root tree has no edges).
* `Fintype.card_le_of_embedding` gives `k <= cardU + cardV` for every good `k`,
  so `Nat.findGreatest` yields a maximal good `k = m`.
* If some vertex is uncovered, connectedness gives a walk from a covered vertex
  to an uncovered one; `SimpleGraph.Walk.exists_boundary_dart` crosses the
  covered set `S`.  On the crossing dart the start is covered and the end is
  uncovered; using `Fin.Embedding.cons` we attach the new vertex as a leaf
  (row attachment if the uncovered vertex is a row, column attachment if it is
  a column), obtaining a strictly larger good `k`, contradicting maximality.
* Both maps are then surjective, hence equivalences; choosing occurrences for
  the tree edges afterwards is injective because equal occurrences would give
  equal endpoint pairs, and `edgeList_nodup` makes equal endpoint pairs equal
  positions.

The row vertex type must be nonempty, since the syntax starts from a row root.
The column and occurrence types may be empty. The occurrence type need not be
finite for the selection theorem.

This proves the spanning-tree selection and completeness bridge needed to apply
the existing syntax-tree partition estimate to connected bipartite multigraphs.
Reindexing that estimate over the original vertices and bounding the unused
occurrences are subsequent steps, not results of this file.
-/

noncomputable section
namespace NLAlib

open scoped BigOperators

variable {U V E : Type*}

/-- The underlying undirected graph of a bipartite multigraph with row vertices
`U`, column vertices `V`, and edge occurrences `E -> (U, V)`: a row and a column
vertex are adjacent iff some occurrence has exactly those endpoints. -/
def _root_.SimpleGraph.bipartiteOccurrenceGraph (sr : E → U) (tg : E → V) :
    SimpleGraph (Sum U V) where
  Adj a b :=
    ∃ (u : U) (v : V),
      (a = Sum.inl u ∧ b = Sum.inr v ∨ a = Sum.inr v ∧ b = Sum.inl u) ∧
        ∃ e : E, sr e = u ∧ tg e = v
  symm := ⟨fun a b h => by
    rcases h with ⟨u, v, hcase, he⟩
    refine ⟨u, v, ?_, he⟩
    rcases hcase with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨u, v, hcase, he⟩
    rcases hcase with h | h
    · exact Sum.inl_ne_inr (h.1.symm.trans h.2)
    · exact Sum.inr_ne_inl (h.1.symm.trans h.2)⟩

/-- A partial attachment of size `k`: a syntax tree `t : RowRootedBipartiteTree
r q` with `k = r + 1 + q`, injective row/column maps into `U`, `V`, such that
every syntax edge is realized by some occurrence. -/
private def Good (sr : E → U) (tg : E → V) (k : ℕ) : Prop :=
  ∃ (r q : ℕ) (t : RowRootedBipartiteTree r q)
    (f : Fin (r+1) ↪ U) (g : Fin q ↪ V),
    k = r + 1 + q ∧
      (∀ i j, (i, j) ∈ t.edgeList →
        ∃ e, sr e = f i ∧ tg e = g j)

/-- Adding a new row leaf: if `u' : U` is uncovered by `f` and `e0` is an
occurrence from `u'` to an already covered column `g j`, then the tree
`addRow t j` with the new row `u'` at index `0` and the new edge `e0` realizes a
strictly larger good attachment. -/
private lemma good_succ_of_row {r q : ℕ} (sr : E → U) (tg : E → V)
    (t : RowRootedBipartiteTree r q)
    (f : Fin (r+1) ↪ U) (g : Fin q ↪ V)
    (hocc : ∀ i j, (i, j) ∈ t.edgeList →
      ∃ e, sr e = f i ∧ tg e = g j)
    (u' : U) (hu' : u' ∉ Set.range f) (j : Fin q) (e0 : E)
    (he0 : sr e0 = u' ∧ tg e0 = g j) :
    Good sr tg (r + 1 + q + 1) := by
  let f' : Fin ((r+1)+1) ↪ U := Fin.Embedding.cons f hu'
  let g' : Fin q ↪ V := g
  refine ⟨r + 1, q, RowRootedBipartiteTree.addRow t j, f', g', ?_, ?_⟩
  · ac_rfl
  · intro i j' hij
    rcases List.mem_cons.mp hij with h | h
    · have hi : i = 0 := congrArg Prod.fst h
      have hj : j' = j := congrArg Prod.snd h
      rw [hi, hj]
      refine ⟨e0, ?_, ?_⟩
      · simp [f', he0.1]
      · simp [g', he0.2]
    · rcases List.mem_map.mp h with ⟨e, he, heeq⟩
      have hi : i = Fin.succ e.1 := (congrArg Prod.fst heeq).symm
      have hj : j' = e.2 := (congrArg Prod.snd heeq).symm
      rcases hocc e.1 e.2 he with ⟨e1, hsr, htg⟩
      refine ⟨e1, ?_, ?_⟩
      · rw [hi]
        simpa [f'] using hsr
      · rw [hj]
        simpa [g'] using htg

/-- Adding a new column leaf: if `v' : V` is uncovered by `g` and `e0` is an
occurrence from an already covered row `f u` to `v'`, then the tree
`addColumn t u` with the new column `v'` at index `0` and the new edge `e0`
realizes a strictly larger good attachment. -/
private lemma good_succ_of_column {r q : ℕ} (sr : E → U) (tg : E → V)
    (t : RowRootedBipartiteTree r q)
    (f : Fin (r+1) ↪ U) (g : Fin q ↪ V)
    (hocc : ∀ i j, (i, j) ∈ t.edgeList →
      ∃ e, sr e = f i ∧ tg e = g j)
    (v' : V) (hv' : v' ∉ Set.range g) (u : Fin (r+1)) (e0 : E)
    (he0 : sr e0 = f u ∧ tg e0 = v') :
    Good sr tg (r + 1 + q + 1) := by
  let g' : Fin (q+1) ↪ V := Fin.Embedding.cons g hv'
  let f' : Fin (r+1) ↪ U := f
  refine ⟨r, q + 1, RowRootedBipartiteTree.addColumn t u, f', g', ?_, ?_⟩
  · ac_rfl
  · intro i j' hij
    rcases List.mem_cons.mp hij with h | h
    · have hi : i = u := congrArg Prod.fst h
      have hj : j' = 0 := congrArg Prod.snd h
      rw [hi, hj]
      refine ⟨e0, ?_, ?_⟩
      · simp [f', he0.1]
      · simp [g', he0.2]
    · rcases List.mem_map.mp h with ⟨e, he, heeq⟩
      have hi : i = e.1 := (congrArg Prod.fst heeq).symm
      have hj : j' = Fin.succ e.2 := (congrArg Prod.snd heeq).symm
      rcases hocc e.1 e.2 he with ⟨e1, hsr, htg⟩
      refine ⟨e1, ?_, ?_⟩
      · rw [hi]
        simpa [f'] using hsr
      · rw [hj]
        simpa [g'] using htg

/-- The root tree alone (no edges) gives a good partial attachment of size `1`
from any root row. -/
private lemma good_one [Nonempty U] (sr : E → U) (tg : E → V) : Good sr tg 1 := by
  classical
  let u0 : U := Classical.choice (inferInstance : Nonempty U)
  let f : Fin 1 ↪ U := ⟨fun _ => u0, by
    intro a b h
    exact Subsingleton.elim a b⟩
  let g : Fin 0 ↪ V := ⟨fun x => x.elim0, by intro a; exact a.elim0⟩
  refine ⟨0, 0, RowRootedBipartiteTree.root, f, g, by norm_num, ?_⟩
  intro i j hij
  simp [RowRootedBipartiteTree.edgeList] at hij

/-- Any good partial attachment has size at most `cardU + cardV`. -/
private lemma good_le_card [Fintype U] [Fintype V] (sr : E → U) (tg : E → V)
    {k : ℕ} (h : Good sr tg k) :
    k ≤ Fintype.card U + Fintype.card V := by
  rcases h with ⟨r, q, t, f, g, rfl, hocc⟩
  have hf : r + 1 ≤ Fintype.card U := by
    simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding f)
  have hg : q ≤ Fintype.card V := by
    simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding g)
  exact add_le_add hf hg

/-- **The bridge.** For every connected bipartite multigraph with finite row and
column vertex sets and indexed edge occurrences `sr : E -> U`, `tg : E -> V`,
there is a syntax tree `t : RowRootedBipartiteTree r q` with equivalences
`ur : Fin (r+1) ≃ U` (rows) and `vc : Fin q ≃ V`
(columns) and an injective occurrence map `occ : Fin t.edgeList.length ↪ E`
such that each tree edge `(i, j)` is realized by the occurrence `occ k`: the
`k`-th edge of `t` has row endpoint `ur i` and column endpoint `vc j`.
The original root index shifts with each row attachment. Column vertices and
edge occurrences may be empty, and finiteness of the occurrence type is not
required. -/
theorem RowRootedBipartiteTree.exists_spanning_tree_syntax
    [Fintype U] [Fintype V] [Nonempty U]
    (sr : E → U) (tg : E → V)
    (hG : (SimpleGraph.bipartiteOccurrenceGraph sr tg).Connected) :
    ∃ (r q : ℕ) (t : RowRootedBipartiteTree r q)
      (ur : Fin (r+1) ≃ U) (vc : Fin q ≃ V)
      (occ : Fin t.edgeList.length ↪ E),
      ∀ k : Fin t.edgeList.length,
        sr (occ k) = ur (t.edgeList.get k).1 ∧
        tg (occ k) = vc (t.edgeList.get k).2 := by
  classical
  let n := Fintype.card U + Fintype.card V
  have hone : Good sr tg 1 := good_one sr tg
  have hone_le : 1 ≤ n := by
    dsimp [n]
    have hpos : 1 ≤ Fintype.card U := Nat.succ_le_of_lt Fintype.card_pos
    exact le_trans hpos (Nat.le_add_right (Fintype.card U) (Fintype.card V))
  let m := Nat.findGreatest (Good sr tg) n
  have hm_good : Good sr tg m := Nat.findGreatest_spec (m := 1) (P := Good sr tg)
    (n := n) hone_le hone
  rcases hm_good with ⟨r, q, t, f, g, hm_eq, hocc⟩
  have hf_surj : Function.Surjective f := by
    by_contra hnsf
    rcases not_forall.mp hnsf with ⟨u, hu⟩
    have hu_notmem : u ∉ Set.range f := by
      simpa [Set.mem_range] using hu
    let S : Set (Sum U V) := Sum.inl '' Set.range f ∪ Sum.inr '' Set.range g
    have hstart : Sum.inl (f 0) ∈ S := by
      left
      exact ⟨f 0, ⟨0, rfl⟩, rfl⟩
    have hend : Sum.inl u ∉ S := by
      intro hmem
      rw [Set.mem_union] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with ⟨x, hx, hxeq⟩
        rcases hx with ⟨i, hi⟩
        have this : u = x := Sum.inl.inj hxeq.symm
        exact hu ⟨i, by rw [this]; exact hi⟩
      · rcases hmem with ⟨v, hv, hveq⟩
        exact Sum.inl_ne_inr hveq.symm
    obtain ⟨p⟩ := hG (Sum.inl (f 0)) (Sum.inl u)
    obtain ⟨d, hdarts, hdfst, hdsnd⟩ := p.exists_boundary_dart S hstart hend
    have hd_adj : (SimpleGraph.bipartiteOccurrenceGraph sr tg).Adj d.fst d.snd := d.adj
    cases hd : d.snd with
    | inl u' =>
        have hu' : u' ∉ Set.range f := by
          intro hmem
          apply hdsnd
          left
          exact ⟨u', hmem, hd.symm⟩
        rcases hd_adj with ⟨u0, v0, hcase, he⟩
        rcases hcase with hcase | hcase
        · exfalso
          exact Sum.inr_ne_inl (hcase.2.symm.trans hd)
        · have hu0 : u0 = u' := Sum.inl.inj (hcase.2.symm.trans hd)
          have hv0 : v0 ∈ Set.range g := by
            rcases hdfst with hdfst | hdfst
            · exfalso
              rcases hdfst with ⟨u1, hu1, heq⟩
              exact Sum.inl_ne_inr (heq.trans hcase.1)
            · rcases hdfst with ⟨v1, hv1, heq⟩
              rcases hv1 with ⟨j, hj⟩
              refine ⟨j, ?_⟩
              have this : v1 = v0 := Sum.inr.inj (heq.trans hcase.1)
              simpa [this] using hj
          rcases hv0 with ⟨j, hj⟩
          rcases he with ⟨e0, he0⟩
          have he0' : sr e0 = u' ∧ tg e0 = g j := by
            constructor
            · simpa [hu0] using he0.1
            · rw [hj]
              exact he0.2
          have hgood_succ : Good sr tg (m + 1) := by
            simpa [hm_eq] using good_succ_of_row sr tg t f g hocc
              u' hu' j e0 he0'
          have hnsf' : ¬ Function.Surjective f := by
            intro hsurj
            exact hu' (hsurj u')
          have hcardU_lt : r + 1 < Fintype.card U := by
            simpa [Fintype.card_fin] using
              (Fintype.card_lt_of_injective_not_surjective f f.injective hnsf')
          have hq : q ≤ Fintype.card V := by
            simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding g)
          have hrm : r + 1 + 1 ≤ Fintype.card U := Nat.succ_le_of_lt hcardU_lt
          have hmle : m + 1 ≤ n := by
            dsimp [n]
            rw [show m + 1 = (r + 1 + 1) + q by
              rw [hm_eq]
              ac_rfl]
            exact add_le_add hrm hq
          have hmle' : m + 1 ≤ m := Nat.le_findGreatest (m := m + 1)
            (P := Good sr tg) (n := n) hmle hgood_succ
          exact (not_lt_of_ge hmle') (Nat.lt_succ_self m)
    | inr v' =>
        have hv' : v' ∉ Set.range g := by
          intro hmem
          apply hdsnd
          right
          exact ⟨v', hmem, hd.symm⟩
        rcases hd_adj with ⟨u0, v0, hcase, he⟩
        rcases hcase with hcase | hcase
        · have hv0 : v0 = v' := Sum.inr.inj (hcase.2.symm.trans hd)
          have hu0 : u0 ∈ Set.range f := by
            rcases hdfst with hdfst | hdfst
            · rcases hdfst with ⟨u1, hu1, heq⟩
              rcases hu1 with ⟨i, hi⟩
              refine ⟨i, ?_⟩
              have this : u1 = u0 := Sum.inl.inj (heq.trans hcase.1)
              simpa [this] using hi
            · exfalso
              rcases hdfst with ⟨v1, hv1, heq⟩
              exact Sum.inr_ne_inl (heq.trans hcase.1)
          rcases hu0 with ⟨i, hi⟩
          rcases he with ⟨e0, he0⟩
          have he0' : sr e0 = f i ∧ tg e0 = v' := by
            constructor
            · rw [hi]
              exact he0.1
            · simpa [hv0] using he0.2
          have hgood_succ : Good sr tg (m + 1) := by
            simpa [hm_eq] using good_succ_of_column sr tg t f g hocc
              v' hv' i e0 he0'
          have hnsg' : ¬ Function.Surjective g := by
            intro hsurj
            exact hv' (hsurj v')
          have hcardV_lt : q < Fintype.card V := by
            simpa [Fintype.card_fin] using
              (Fintype.card_lt_of_injective_not_surjective g g.injective hnsg')
          have hf : r + 1 ≤ Fintype.card U := by
            simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding f)
          have hq : q + 1 ≤ Fintype.card V := Nat.succ_le_of_lt hcardV_lt
          have hmle : m + 1 ≤ n := by
            dsimp [n]
            rw [show m + 1 = (r + 1) + (q + 1) by
              rw [hm_eq]
              ac_rfl]
            exact add_le_add hf hq
          have hmle' : m + 1 ≤ m := Nat.le_findGreatest (m := m + 1)
            (P := Good sr tg) (n := n) hmle hgood_succ
          exact (not_lt_of_ge hmle') (Nat.lt_succ_self m)
        · exfalso
          exact Sum.inl_ne_inr (hcase.2.symm.trans hd)
  have hg_surj : Function.Surjective g := by
    by_contra hnsg
    rcases not_forall.mp hnsg with ⟨v, hv⟩
    have hv_notmem : v ∉ Set.range g := by
      simpa [Set.mem_range] using hv
    let S : Set (Sum U V) := Sum.inl '' Set.range f ∪ Sum.inr '' Set.range g
    have hstart : Sum.inl (f 0) ∈ S := by
      left
      exact ⟨f 0, ⟨0, rfl⟩, rfl⟩
    have hend : Sum.inr v ∉ S := by
      intro hmem
      rw [Set.mem_union] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with ⟨x, hx, hxeq⟩
        exact Sum.inl_ne_inr hxeq
      · rcases hmem with ⟨w, hw, hweq⟩
        rcases hw with ⟨j, hj⟩
        have this : v = w := Sum.inr.inj hweq.symm
        exact hv ⟨j, by rw [this]; exact hj⟩
    obtain ⟨p⟩ := hG (Sum.inl (f 0)) (Sum.inr v)
    obtain ⟨d, hdarts, hdfst, hdsnd⟩ := p.exists_boundary_dart S hstart hend
    have hd_adj : (SimpleGraph.bipartiteOccurrenceGraph sr tg).Adj d.fst d.snd := d.adj
    cases hd : d.snd with
    | inl u' =>
        have hu' : u' ∉ Set.range f := by
          intro hmem
          apply hdsnd
          left
          exact ⟨u', hmem, hd.symm⟩
        rcases hd_adj with ⟨u0, v0, hcase, he⟩
        rcases hcase with hcase | hcase
        · exfalso
          exact Sum.inr_ne_inl (hcase.2.symm.trans hd)
        · have hu0 : u0 = u' := Sum.inl.inj (hcase.2.symm.trans hd)
          have hv0 : v0 ∈ Set.range g := by
            rcases hdfst with hdfst | hdfst
            · exfalso
              rcases hdfst with ⟨u1, hu1, heq⟩
              exact Sum.inl_ne_inr (heq.trans hcase.1)
            · rcases hdfst with ⟨v1, hv1, heq⟩
              rcases hv1 with ⟨j, hj⟩
              refine ⟨j, ?_⟩
              have this : v1 = v0 := Sum.inr.inj (heq.trans hcase.1)
              simpa [this] using hj
          rcases hv0 with ⟨j, hj⟩
          rcases he with ⟨e0, he0⟩
          have he0' : sr e0 = u' ∧ tg e0 = g j := by
            constructor
            · simpa [hu0] using he0.1
            · rw [hj]
              exact he0.2
          have hgood_succ : Good sr tg (m + 1) := by
            simpa [hm_eq] using good_succ_of_row sr tg t f g hocc
              u' hu' j e0 he0'
          have hnsf' : ¬ Function.Surjective f := by
            intro hsurj
            exact hu' (hsurj u')
          have hcardU_lt : r + 1 < Fintype.card U := by
            simpa [Fintype.card_fin] using
              (Fintype.card_lt_of_injective_not_surjective f f.injective hnsf')
          have hq : q ≤ Fintype.card V := by
            simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding g)
          have hrm : r + 1 + 1 ≤ Fintype.card U := Nat.succ_le_of_lt hcardU_lt
          have hmle : m + 1 ≤ n := by
            dsimp [n]
            rw [show m + 1 = (r + 1 + 1) + q by
              rw [hm_eq]
              ac_rfl]
            exact add_le_add hrm hq
          have hmle' : m + 1 ≤ m := Nat.le_findGreatest (m := m + 1)
            (P := Good sr tg) (n := n) hmle hgood_succ
          exact (not_lt_of_ge hmle') (Nat.lt_succ_self m)
    | inr v' =>
        have hv' : v' ∉ Set.range g := by
          intro hmem
          apply hdsnd
          right
          exact ⟨v', hmem, hd.symm⟩
        rcases hd_adj with ⟨u0, v0, hcase, he⟩
        rcases hcase with hcase | hcase
        · have hv0 : v0 = v' := Sum.inr.inj (hcase.2.symm.trans hd)
          have hu0 : u0 ∈ Set.range f := by
            rcases hdfst with hdfst | hdfst
            · rcases hdfst with ⟨u1, hu1, heq⟩
              rcases hu1 with ⟨i, hi⟩
              refine ⟨i, ?_⟩
              have this : u1 = u0 := Sum.inl.inj (heq.trans hcase.1)
              simpa [this] using hi
            · exfalso
              rcases hdfst with ⟨v1, hv1, heq⟩
              exact Sum.inr_ne_inl (heq.trans hcase.1)
          rcases hu0 with ⟨i, hi⟩
          rcases he with ⟨e0, he0⟩
          have he0' : sr e0 = f i ∧ tg e0 = v' := by
            constructor
            · rw [hi]
              exact he0.1
            · simpa [hv0] using he0.2
          have hgood_succ : Good sr tg (m + 1) := by
            simpa [hm_eq] using good_succ_of_column sr tg t f g hocc
              v' hv' i e0 he0'
          have hnsg' : ¬ Function.Surjective g := by
            intro hsurj
            exact hv' (hsurj v')
          have hcardV_lt : q < Fintype.card V := by
            simpa [Fintype.card_fin] using
              (Fintype.card_lt_of_injective_not_surjective g g.injective hnsg')
          have hf : r + 1 ≤ Fintype.card U := by
            simpa [Fintype.card_fin] using (Fintype.card_le_of_embedding f)
          have hq : q + 1 ≤ Fintype.card V := Nat.succ_le_of_lt hcardV_lt
          have hmle : m + 1 ≤ n := by
            dsimp [n]
            rw [show m + 1 = (r + 1) + (q + 1) by
              rw [hm_eq]
              ac_rfl]
            exact add_le_add hf hq
          have hmle' : m + 1 ≤ m := Nat.le_findGreatest (m := m + 1)
            (P := Good sr tg) (n := n) hmle hgood_succ
          exact (not_lt_of_ge hmle') (Nat.lt_succ_self m)
        · exfalso
          exact Sum.inl_ne_inr (hcase.2.symm.trans hd)
  let ur : Fin (r+1) ≃ U := Equiv.ofBijective f ⟨f.injective, hf_surj⟩
  let vc : Fin q ≃ V := Equiv.ofBijective g ⟨g.injective, hg_surj⟩
  let occFun : Fin t.edgeList.length → E :=
    fun k => Classical.choose
      (hocc (t.edgeList.get k).1 (t.edgeList.get k).2
        (List.get_mem (t.edgeList) k))
  let occFinal : Fin t.edgeList.length ↪ E :=
    ⟨occFun, by
      intro k1 k2 h
      have hs1 := Classical.choose_spec
        (hocc (t.edgeList.get k1).1 (t.edgeList.get k1).2
          (List.get_mem (t.edgeList) k1))
      have hs2 := Classical.choose_spec
        (hocc (t.edgeList.get k2).1 (t.edgeList.get k2).2
          (List.get_mem (t.edgeList) k2))
      have hrow : (t.edgeList.get k1).1 = (t.edgeList.get k2).1 := by
        apply f.injective
        calc
          f (t.edgeList.get k1).1 = sr (occFun k1) := hs1.1.symm
          _ = sr (occFun k2) := by rw [h]
          _ = f (t.edgeList.get k2).1 := hs2.1
      have hcol : (t.edgeList.get k1).2 = (t.edgeList.get k2).2 := by
        apply g.injective
        calc
          g (t.edgeList.get k1).2 = tg (occFun k1) := hs1.2.symm
          _ = tg (occFun k2) := by rw [h]
          _ = g (t.edgeList.get k2).2 := hs2.2
      have hedge : t.edgeList.get k1 = t.edgeList.get k2 := Prod.ext hrow hcol
      exact (RowRootedBipartiteTree.edgeList_nodup t).injective_get hedge⟩
  refine ⟨r, q, t, ur, vc, occFinal, ?_⟩
  intro k
  have hspec := Classical.choose_spec
    (hocc (t.edgeList.get k).1 (t.edgeList.get k).2
      (List.get_mem (t.edgeList) k))
  constructor
  · calc
      sr (occFinal k) = f (t.edgeList.get k).1 := hspec.1
      _ = ur (t.edgeList.get k).1 := by
        simp [ur, Equiv.ofBijective]
  · calc
      tg (occFinal k) = g (t.edgeList.get k).2 := hspec.2
      _ = vc (t.edgeList.get k).2 := by
        simp [vc, Equiv.ofBijective]

end NLAlib

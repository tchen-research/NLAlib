import NLAlib.ForMathlib.Combinatorics.StationaryTree
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Leaf-grown spanning trees

Every finite connected graph with at least two vertices has a spanning tree
in the leaf-attachment syntax. The proof grows a maximal partial attachment;
a walk to an uncovered vertex supplies the next boundary edge.
-/

noncomputable section

namespace NLAlib.LeafTree

variable {V : Type*} [Fintype V]

private def Good (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (n : ℕ) (t : LeafTree n) (f : Fin (n + 2) ↪ V), k = n + 2 ∧
    ∀ e ∈ t.edgeList, G.Adj (f e.1) (f e.2)

omit [Fintype V] in
private theorem good_two [Nontrivial V] (G : SimpleGraph V) (hG : G.Connected) :
    Good G 2 := by
  classical
  let u : V := Classical.arbitrary V
  obtain ⟨v, huv⟩ := hG.preconnected.exists_adj_of_nontrivial u
  let f : Fin 2 ↪ V := ⟨![u, v], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (huv.ne hij).elim
    · exact (huv.ne hij.symm).elim
    · rfl⟩
  refine ⟨0, edge, f, rfl, ?_⟩
  intro e he
  have heq : e = (0, 1) := List.mem_singleton.mp he
  rw [heq]
  exact huv

omit [Fintype V] in
private theorem good_succ {G : SimpleGraph V} {n : ℕ}
    (t : LeafTree n) (f : Fin (n + 2) ↪ V)
    (ht : ∀ e ∈ t.edgeList, G.Adj (f e.1) (f e.2))
    (u : V) (hu : u ∉ Set.range f) (p : Fin (n + 2))
    (hpu : G.Adj (f p) u) : Good G (n + 2 + 1) := by
  classical
  let f' := Fin.Embedding.cons f hu
  refine ⟨n + 1, attach t p, f', by omega, ?_⟩
  intro e he
  rcases List.mem_cons.mp he with he | he
  · simpa [he, f'] using hpu
  · rcases List.mem_map.mp he with ⟨e', he', rfl⟩
    simpa [f'] using ht e' he'

/-- Every finite connected graph with at least two vertices has a spanning
tree built from one edge by leaf attachments, together with an equivalence
between the tree vertices and the original vertices preserving all tree edges. -/
theorem exists_spanning_tree [Nontrivial V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ (n : ℕ) (t : LeafTree n) (f : Fin (n + 2) ≃ V),
      ∀ e ∈ t.edgeList, G.Adj (f e.1) (f e.2) := by
  classical
  have htwo := good_two G hG
  have htwole : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  let m := Nat.findGreatest (Good G) (Fintype.card V)
  have hgood : Good G m := Nat.findGreatest_spec htwole htwo
  obtain ⟨n, t, f, hm, ht⟩ := hgood
  have hsurj : Function.Surjective f := by
    by_contra hnot
    obtain ⟨u, hu⟩ := not_forall.mp hnot
    have hout : u ∉ Set.range f := hu
    obtain ⟨p⟩ := hG (f 0) u
    obtain ⟨dart, _hmem, hin, hout'⟩ := p.exists_boundary_dart (Set.range f) ⟨0, rfl⟩ hout
    obtain ⟨i, hi⟩ := hin
    have hadj : G.Adj (f i) dart.snd := hi ▸ dart.adj
    have hnext : Good G (m + 1) := by
      simpa only [hm] using good_succ t f ht dart.snd hout' i hadj
    have hlt : n + 2 < Fintype.card V := by
      simpa only [Fintype.card_fin] using
        Fintype.card_lt_of_injective_not_surjective f f.injective hnot
    have hmle : m + 1 ≤ Fintype.card V := by omega
    have hbad : m + 1 ≤ m := Nat.le_findGreatest hmle hnext
    omega
  exact ⟨n, t, Equiv.ofBijective f ⟨f.injective, hsurj⟩, ht⟩

/-- The unordered edges in a leaf-grown tree are pairwise distinct. -/
theorem edgeList_sym2_nodup {n : ℕ} (t : LeafTree n) :
    (t.edgeList.map (fun e => s(e.1, e.2))).Nodup := by
  induction t with
  | edge => simp [edgeList]
  | @attach n t p ih =>
      simp only [edgeList, List.map_cons, List.map_map]
      refine List.Nodup.cons ?_ ?_
      · intro hmem
        obtain ⟨e, _he, heq⟩ := List.mem_map.mp hmem
        rcases Sym2.eq_iff.mp heq with h | h
        · exact Fin.succ_ne_zero _ h.2
        · exact Fin.succ_ne_zero _ h.1
      · have hmap :
            t.edgeList.map (fun e => s(e.1.succ, e.2.succ)) =
              (t.edgeList.map (fun e => s(e.1, e.2))).map (Sym2.map Fin.succ) := by
          rw [List.map_map]
          rfl
        change (t.edgeList.map (fun e => s(e.1.succ, e.2.succ))).Nodup
        rw [hmap]
        exact ih.map (Sym2.map.injective (Fin.succ_injective _))

end NLAlib.LeafTree

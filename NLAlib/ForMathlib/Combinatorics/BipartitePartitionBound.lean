import NLAlib.ForMathlib.Combinatorics.BipartiteSpanningTree
import Mathlib.Algebra.BigOperators.Fin

/-!
# Universal partition-sum bound for connected bipartite multigraphs

This file uses the spanning-tree construction to prove that for every connected
bipartite multigraph with finite row and column sets `U`, `V`, nonempty `U`, and edge
occurrences `sr : E -> U`, `tg : E -> V`, the sum over all labelings of the
product of the edge weights is bounded by

```
(Fintype.card I : ℝ) * a ^ (Fintype.card U - 1) * c ^ (Fintype.card V) *
  s ^ (Fintype.card E - (Fintype.card U - 1 + Fintype.card V))
```

when every `w i j` is nonnegative, bounded by `s`, every column sum is at most
`a`, and every row sum is at most `c`.

The proof selects a spanning tree via `exists_spanning_tree_syntax`, reindexes
the row and column labelings through the row/column equivalences
`ur : Fin (r+1) ≃ U`, `vc : Fin q ≃ V`, bounds the off-tree factors by
`s ^ O.card` using `prod_bipartite_edge_weight_le_prod_mul_pow`, and applies the tree
bound `partitionSum_le`.

The leading factor is the cardinality of the label type `I` (the number of free
root-row labels), not of the vertex type `U`. The `[DecidableEq U]` and
`[DecidableEq V]` assumptions are classical decidability assumptions providing
the `Fintype` instances for the function label spaces `U -> I`, `V -> J`.
-/

noncomputable section
namespace NLAlib

open scoped BigOperators
open Finset

variable {U V E I J : Type*}

/-- The product over the occurrence-indexed tree edges equals the syntax-tree
weight: if the injective occurrence map `occ` realizes each tree edge `(i, j)`
by an occurrence with endpoints `ur i`, `vc j`, then the product of the weights
over `univ.map occ` equals `weight w t X Y`. -/
theorem prod_bipartite_tree_edges_eq_weight [Fintype E] [DecidableEq E]
    {r q : ℕ} (t : RowRootedBipartiteTree r q)
    (sr : E → U) (tg : E → V)
    (ur : Fin (r+1) ≃ U) (vc : Fin q ≃ V)
    (occ : Fin t.edgeList.length ↪ E)
    (hend : ∀ k : Fin t.edgeList.length,
      sr (occ k) = ur (t.edgeList.get k).1 ∧
        tg (occ k) = vc (t.edgeList.get k).2)
    (w : I → J → ℝ)
    (X : Fin (r+1) → I) (Y : Fin q → J) :
    (∏ e ∈ univ.map occ, w (X (ur.symm (sr e))) (Y (vc.symm (tg e)))) =
      RowRootedBipartiteTree.weight w t X Y := by
  unfold RowRootedBipartiteTree.weight
  calc
    (∏ e ∈ univ.map occ, w (X (ur.symm (sr e))) (Y (vc.symm (tg e))))
        = univ.prod (fun k : Fin t.edgeList.length =>
            w (X (ur.symm (sr (occ k)))) (Y (vc.symm (tg (occ k))))) := by
          rw [Finset.prod_map]
    _ = univ.prod (fun k : Fin t.edgeList.length =>
            w (X (t.edgeList.get k).1) (Y (t.edgeList.get k).2)) := by
          refine Finset.prod_congr rfl ?_
          intro k hk
          rcases hend k with ⟨hk1, hk2⟩
          rw [hk1, hk2]
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    _ = (List.ofFn (fun k : Fin t.edgeList.length =>
            w (X (t.edgeList.get k).1) (Y (t.edgeList.get k).2))).prod := by
          rw [← List.prod_ofFn]
    _ = (t.edgeList.map (fun e => w (X e.1) (Y e.2))).prod := by
          rw [List.ofFn_comp' (f := fun k : Fin t.edgeList.length => t.edgeList.get k)
            (g := fun e => w (X e.1) (Y e.2))]
          rw [List.ofFn_get]

/-- **Universal partition-sum bound.** For every connected bipartite multigraph
with finite nonempty row set `U`, finite column set `V`, and indexed edge occurrences
`sr : E -> U`, `tg : E -> V`, if `w` is nonnegative, every column sum of `w`
is at most `a`, every row sum is at most `c`, and every entry is at most `s`,
then the unrestricted sum over all labelings of the product over all edge
occurrences is at most

```
(Fintype.card I : ℝ) * a ^ (Fintype.card U - 1) * c ^ (Fintype.card V) *
  s ^ (Fintype.card E - (Fintype.card U - 1 + Fintype.card V))
```

The exponent of `s` is the number of edges outside a spanning tree: the tree has
`Fintype.card U - 1 + Fintype.card V` edges, so the off-tree count is
`Fintype.card E - (Fintype.card U - 1 + Fintype.card V)`. -/
theorem sum_prod_bipartite_edge_weight_le_of_connected [Fintype U] [Fintype V] [Nonempty U]
    [Fintype E] [DecidableEq E] [DecidableEq U] [DecidableEq V]
    [Fintype I] [Fintype J]
    (sr : E → U) (tg : E → V)
    (hG : (SimpleGraph.bipartiteOccurrenceGraph sr tg).Connected)
    (w : I → J → ℝ) (a c s : ℝ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ c)
    (hw : ∀ i j, w i j ≤ s)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    (∑ x : U → I, ∑ y : V → J,
       ∏ e : E, w (x (sr e)) (y (tg e))) ≤
      (Fintype.card I : ℝ) * a ^ (Fintype.card U - 1) *
        c ^ (Fintype.card V) *
        s ^ (Fintype.card E - (Fintype.card U - 1 + Fintype.card V)) := by
  classical
  obtain ⟨r, q, t, ur, vc, occ, hend⟩ :=
    RowRootedBipartiteTree.exists_spanning_tree_syntax (U := U) (V := V)
      (E := E) sr tg hG
  let T : Finset E := univ.map occ
  let O : Finset E := Tᶜ
  have hcardU : Fintype.card U = r + 1 := by
    simpa [Fintype.card_fin] using (Fintype.card_congr ur).symm
  have hcardV : Fintype.card V = q := by
    simpa [Fintype.card_fin] using (Fintype.card_congr vc).symm
  have hlen : t.edgeList.length = r + q := RowRootedBipartiteTree.edgeList_length t
  have hTcard : T.card = r + q := by
    simp [T, hlen]
  have hOcard : O.card = Fintype.card E - (r + q) := by
    dsimp [O]
    rw [Finset.card_compl, hTcard]
  have hdisj : Disjoint T O := by
    rw [Finset.disjoint_left]
    intro e heT heO
    have henot : e ∉ T := by simpa [O] using heO
    exact henot heT
  have huni : T ∪ O = univ := by
    simp [O]
  have hTprod : ∀ (X : Fin (r+1) → I) (Y : Fin q → J),
      (∏ e ∈ T, w (X (ur.symm (sr e))) (Y (vc.symm (tg e)))) =
        RowRootedBipartiteTree.weight w t X Y := by
    intro X Y
    dsimp [T]
    exact prod_bipartite_tree_edges_eq_weight t sr tg ur vc occ hend w X Y
  have hsplit : ∀ (X : Fin (r+1) → I) (Y : Fin q → J),
      (∏ e : E, w (X (ur.symm (sr e))) (Y (vc.symm (tg e)))) ≤
        RowRootedBipartiteTree.weight w t X Y * s ^ O.card := by
    intro X Y
    calc
      (∏ e : E, w (X (ur.symm (sr e))) (Y (vc.symm (tg e))))
          ≤ (∏ e ∈ T, w (X (ur.symm (sr e))) (Y (vc.symm (tg e)))) * s ^ O.card := by
            exact prod_bipartite_edge_weight_le_prod_mul_pow (w := w) (s := s) hwnn hw
              T O hdisj huni sr tg (fun u => X (ur.symm u)) (fun v => Y (vc.symm v))
      _ = RowRootedBipartiteTree.weight w t X Y * s ^ O.card := by
            congr 1
            exact hTprod X Y
  have hr : r = Fintype.card U - 1 := by
    rw [hcardU, Nat.add_sub_cancel]
  have hq' : q = Fintype.card V := by
    exact hcardV.symm
  have hO : O.card = Fintype.card E - (Fintype.card U - 1 + Fintype.card V) := by
    rw [hOcard, ← hr, ← hq']
  calc
    (∑ x : U → I, ∑ y : V → J,
        ∏ e : E, w (x (sr e)) (y (tg e)))
    = ∑ X : Fin (r+1) → I, ∑ y : V → J,
        ∏ e : E, w (X (ur.symm (sr e))) (y (tg e)) := by
        exact (Equiv.sum_comp (Equiv.arrowCongr ur (Equiv.refl I))
          (g := fun x : U → I =>
            ∑ y : V → J, ∏ e : E, w (x (sr e)) (y (tg e)))).symm
    _ = ∑ X : Fin (r+1) → I, ∑ Y : Fin q → J,
        ∏ e : E, w (X (ur.symm (sr e))) (Y (vc.symm (tg e))) := by
        refine Finset.sum_congr rfl ?_
        intro X hX
        exact (Equiv.sum_comp (Equiv.arrowCongr vc (Equiv.refl J))
          (g := fun y : V → J =>
            ∏ e : E, w (X (ur.symm (sr e))) (y (tg e)))).symm
    _ ≤ ∑ X : Fin (r+1) → I, ∑ Y : Fin q → J,
        RowRootedBipartiteTree.weight w t X Y * s ^ O.card := by
        refine Finset.sum_le_sum ?_
        intro X hX
        refine Finset.sum_le_sum ?_
        intro Y hY
        exact hsplit X Y
    _ = (∑ X : Fin (r+1) → I, ∑ Y : Fin q → J,
          RowRootedBipartiteTree.weight w t X Y) * s ^ O.card := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro X hX
        rw [Finset.sum_mul]
    _ = RowRootedBipartiteTree.partitionSum t w * s ^ O.card := by
        rfl
    _ ≤ ((Fintype.card I : ℝ) * a ^ r * c ^ q) * s ^ O.card := by
        exact mul_le_mul_of_nonneg_right
          (RowRootedBipartiteTree.partitionSum_le t w a c hwnn hcol hrow ha hc)
          (pow_nonneg hs O.card)
    _ = (Fintype.card I : ℝ) * a ^ (Fintype.card U - 1) *
          c ^ (Fintype.card V) * s ^ (Fintype.card E -
            (Fintype.card U - 1 + Fintype.card V)) := by
        rw [hr, hq', hO]

end NLAlib

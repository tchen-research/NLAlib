import NLAlib.ForMathlib.Combinatorics.LeafTreeSpanningTree
import NLAlib.ForMathlib.Combinatorics.TreePartitionHolder

/-!
# Profile-sensitive weighted graph partition functions

Connected finite graphs with indexed edge occurrences admit a leaf-grown
spanning tree. Non-tree factors are charged to their initial endpoints;
the stationary-tree Hölder estimate retains the sums of degree powers and
row-maximum powers rather than replacing these by uniform maxima.

The resulting inequality is the integer-edge version of Latała–van Handel–
Youssef, arXiv:1711.00807v2, Theorem 2.8, with a stationary-tree proof.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib

/-- The undirected simple graph underlying an indexed family of directed
edge occurrences. Parallel occurrences are allowed and loops are discarded. -/
def _root_.SimpleGraph.indexedOccurrenceGraph {V E : Type*} (src dst : E → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)
  symm := ⟨by
    intro u v h
    obtain ⟨hne, e, he⟩ := h
    exact ⟨hne.symm, e, he.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

namespace LeafTree

variable {V E : Type*} [Fintype V] [Nontrivial V]

/-- A spanning tree can choose distinct actual edge occurrences, including
their original orientations up to endpoint exchange. Thus parallel edges
remain distinct factors and are never silently identified. -/
theorem exists_spanning_tree_occurrences
    (src dst : E → V)
    (hG : (SimpleGraph.indexedOccurrenceGraph src dst).Connected) :
    ∃ (n : ℕ) (t : LeafTree n) (f : Fin (n + 2) ≃ V)
      (occ : Fin t.edgeList.length ↪ E),
      ∀ k, s(src (occ k), dst (occ k)) =
        s(f (t.edgeList.get k).1, f (t.edgeList.get k).2) := by
  classical
  obtain ⟨n, t, f, ht⟩ := exists_spanning_tree (SimpleGraph.indexedOccurrenceGraph src dst) hG
  have hex (k : Fin t.edgeList.length) :
      ∃ e : E, s(src e, dst e) = s(f (t.edgeList.get k).1, f (t.edgeList.get k).2) := by
    obtain ⟨_hne, e, he⟩ := ht (t.edgeList.get k) (List.get_mem _ _)
    exact ⟨e, Sym2.eq_iff.mpr he⟩
  choose occ hocc using hex
  have hkey : Function.Injective (fun k : Fin t.edgeList.length =>
      s((t.edgeList.get k).1, (t.edgeList.get k).2)) := by
    intro k l hkl
    have heq :
        (t.edgeList.map (fun e => s(e.1, e.2))).get ⟨k.val, by simp⟩ =
          (t.edgeList.map (fun e => s(e.1, e.2))).get ⟨l.val, by simp⟩ := by
      simpa only [List.get_eq_getElem, List.getElem_map] using hkl
    have hindices := t.edgeList_sym2_nodup.injective_get heq
    have hh : k.val = l.val := congrArg (fun z => z.val) hindices
    exact Fin.ext hh
  have hinj : Function.Injective occ := by
    intro k l hkl
    apply hkey
    apply Sym2.map.injective f.injective
    change s(f (t.edgeList.get k).1, f (t.edgeList.get k).2) =
      s(f (t.edgeList.get l).1, f (t.edgeList.get l).2)
    rw [← hocc k, ← hocc l, hkl]
  exact ⟨n, t, f, ⟨occ, hinj⟩, hocc⟩

end LeafTree

variable {V E α : Type*} [Fintype V] [Nontrivial V] [Fintype E] [Fintype α] [DecidableEq V]

/-- A connected multigraph partition is bounded by degree and entry-profile
power sums with constant one. If there are `p` edge occurrences and `v`
vertices, the degree norm has exponent `v - 1` and the row-entry cap norm has
exponent `p - v + 1`. This retains the full profile geometry.

Source: Latała–van Handel–Youssef, arXiv:1711.00807v2, Theorem 2.8,
integer even edge exponents. The proof uses a stationary tree-indexed chain
after selecting an ordinary spanning tree. -/
theorem sum_prod_edge_weight_le_of_connected
    (src dst : E → V) (hG : (SimpleGraph.indexedOccurrenceGraph src dst).Connected)
    (hp : 0 < Fintype.card E)
    (w : α → α → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsymm : ∀ i j, w i j = w j i)
    (s : α → ℝ) (hcap : ∀ i j, w i j ≤ s i)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hda : (∑ i, (∑ j, w i j) ^ Fintype.card E) ≤ a ^ Fintype.card E)
    (hsb : (∑ i, s i ^ Fintype.card E) ≤ b ^ Fintype.card E) :
    (∑ x : V → α, ∏ e : E, w (x (src e)) (x (dst e))) ≤
      a ^ (Fintype.card V - 1) * b ^ (Fintype.card E - (Fintype.card V - 1)) := by
  classical
  by_cases hD : 0 < ∑ i, ∑ j, w i j
  case neg =>
    have hzero : (∑ i, ∑ j, w i j) = 0 := le_antisymm (le_of_not_gt hD)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hw i j)
    have hwzero (i j : α) : w i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw i j)).mp
        ((Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg fun j _ => hw i j)).mp hzero i (by simp)) j (by simp)
    simp only [hwzero, Finset.prod_const, Finset.card_univ, zero_pow (Nat.ne_of_gt hp),
      Finset.sum_const_zero]
    positivity
  obtain ⟨n, t, f, occ, hend⟩ := LeafTree.exists_spanning_tree_occurrences src dst hG
  let T : Finset E := Finset.univ.map occ
  let O : Finset E := Tᶜ
  let c : ℕ := O.card
  let q : Fin (n + 2) → ℕ := fun v => (O.filter (fun e => f.symm (src e) = v)).card
  have hq : ∑ v, q v = c := by
    simpa only [q, Finset.filter_mem_eq_inter, Finset.filter_true_of_mem,
      Finset.mem_univ, Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter O Finset.univ (fun e => f.symm (src e))
  have hcardV : Fintype.card V = n + 2 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr f).symm
  have hTcard : T.card = n + 1 := by simp only [T, Finset.card_map, Finset.card_univ, Fintype.card_fin, t.edgeList_length]
  have hOcard : c = Fintype.card E - (n + 1) := by
    simp only [c, O, Finset.card_compl, hTcard]
  have hTle : n + 1 ≤ Fintype.card E := by
    rw [← hTcard]
    exact Finset.card_le_univ T
  have htotal : n + c + 1 = Fintype.card E := by omega
  have hs (i : α) : 0 ≤ s i := (hw i i).trans (hcap i i)
  have hTprod (X : Fin (n + 2) → α) :
      (∏ e ∈ T, w (X (f.symm (src e))) (X (f.symm (dst e)))) = t.edgeWeight w X := by
    rw [Finset.prod_map]
    have hterm (k : Fin t.edgeList.length) :
        w (X (f.symm (src (occ k)))) (X (f.symm (dst (occ k)))) =
          w (X (t.edgeList.get k).1) (X (t.edgeList.get k).2) := by
      rcases Sym2.eq_iff.mp (hend k) with h | h
      · rw [h.1, h.2, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      · rw [h.1, h.2, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hsymm]
    simp_rw [hterm]
    rw [t.edgeWeight_eq_prod_edgeList, ← List.prod_ofFn]
    congr 1
    rw [List.ofFn_comp' (f := fun k : Fin t.edgeList.length => t.edgeList.get k)
      (g := fun e => w (X e.1) (X e.2)), List.ofFn_get]
  have hOprod (X : Fin (n + 2) → α) :
      (∏ e ∈ O, s (X (f.symm (src e)))) = ∏ v, s (X v) ^ q v := by
    symm
    simpa only [Finset.prod_const, q] using
      Finset.prod_fiberwise' O (fun e => f.symm (src e)) (fun v => s (X v))
  have hsplit (X : Fin (n + 2) → α) :
      (∏ e : E, w (X (f.symm (src e))) (X (f.symm (dst e)))) ≤
        t.edgeWeight w X * ∏ v, s (X v) ^ q v := by
    rw [← Finset.prod_mul_prod_compl T, hTprod, ← hOprod]
    apply mul_le_mul_of_nonneg_left ?_ (t.edgeWeight_nonneg w hw X)
    exact Finset.prod_le_prod (fun e _ => hw _ _) (fun e _ => hcap _ _)
  have htree := t.sum_edgeWeight_mul_prod_pow_le_of_power_sums w hw hsymm hD s hs q c hq a b ha hb
    (by simpa only [htotal] using hda) (by simpa only [htotal] using hsb)
  calc
    (∑ x : V → α, ∏ e : E, w (x (src e)) (x (dst e))) =
        ∑ X : Fin (n + 2) → α, ∏ e : E, w (X (f.symm (src e))) (X (f.symm (dst e))) := by
      exact (Equiv.sum_comp (Equiv.arrowCongr f (Equiv.refl α))
        (fun x : V → α => ∏ e : E, w (x (src e)) (x (dst e)))).symm
    _ ≤ ∑ X : Fin (n + 2) → α, t.edgeWeight w X * ∏ v, s (X v) ^ q v :=
      Finset.sum_le_sum fun X _ => hsplit X
    _ ≤ a ^ (n + 1) * b ^ c := htree
    _ = _ := by rw [hcardV, show n + 2 - 1 = n + 1 by omega, hOcard]

end NLAlib

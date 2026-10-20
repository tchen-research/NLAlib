import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Function.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import NLAlib.ForMathlib.Combinatorics.BipartiteSpanningTree

/-!
# Pairing quotients of bipartite occurrence graphs

For row and column endpoint maps and pairs of original occurrences, quotienting
by paired endpoint identifications gives an exact equivalence between quotient
labels and admissible original labels. Consequently the sum of products with
local equality indicators is exactly the quotient partition sum. Labels are
arbitrary functions and weights are arbitrary real numbers; empty label types
and additional coincidences are allowed.

An endpoint-cover bijection gives a surjective graph homomorphism to the paired
quotient. For the alternating Gram cycle, connectedness is proved directly from
`row t -- col t -- row (finRotate p t)`, including `p = 1`. This is deterministic
infrastructure for `independent-entry-gaussian-extremum`; it does not prove that
atlas target or invoke any Gaussian probability result.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib.PairingQuotient

variable {R C O E I J : Type*}

-- ---------------------------------------------------------------- definitions

/-- Row generating relation of a pairing: two rows are related if they are the
row endpoints `sr (alpha e)`, `sr (beta e)` of one paired pair `e`. -/
def RowRel (sr : O → R) (alpha beta : E → O) (r r' : R) : Prop :=
  ∃ e : E, sr (alpha e) = r ∧ sr (beta e) = r'

/-- Column generating relation of a pairing: two columns are related if they are
the column endpoints `tg (alpha e)`, `tg (beta e)` of one paired pair `e`. -/
def ColRel (tg : O → C) (alpha beta : E → O) (c c' : C) : Prop :=
  ∃ e : E, tg (alpha e) = c ∧ tg (beta e) = c'

/-- The row quotient equivalence: the equivalence closure of `RowRel`. -/
def rowSetoid (sr : O → R) (alpha beta : E → O) : Setoid R :=
  Relation.EqvGen.setoid (RowRel sr alpha beta)

/-- The column quotient equivalence: the equivalence closure of `ColRel`. -/
def colSetoid (tg : O → C) (alpha beta : E → O) : Setoid C :=
  Relation.EqvGen.setoid (ColRel tg alpha beta)

/-- `U`: the quotient of the rows by `rowSetoid`. -/
abbrev RowQuotient (sr : O → R) (alpha beta : E → O) :=
  Quotient (rowSetoid sr alpha beta)

/-- `V`: the quotient of the columns by `colSetoid`. -/
abbrev ColQuotient (tg : O → C) (alpha beta : E → O) :=
  Quotient (colSetoid tg alpha beta)

/-- The row endpoint class of the paired pair `e`, i.e. the class of
`sr (alpha e)`. -/
def rowEnd (sr : O → R) (alpha beta : E → O) (e : E) : RowQuotient sr alpha beta :=
  Quotient.mk'' (sr (alpha e))

/-- The column endpoint class of the paired pair `e`, i.e. the class of
`tg (alpha e)`. -/
def colEnd (tg : O → C) (alpha beta : E → O) (e : E) : ColQuotient tg alpha beta :=
  Quotient.mk'' (tg (alpha e))

/-- A pair of original labels `x : R → I`, `y : C → J` is admissible when every
paired pair identifies the labels of its two row endpoints and of its two column
endpoints. -/
def Admissible (sr : O → R) (tg : O → C) (alpha beta : E → O)
    (x : R → I) (y : C → J) : Prop :=
  ∀ e : E, x (sr (alpha e)) = x (sr (beta e)) ∧
    y (tg (alpha e)) = y (tg (beta e))

-- --------------------------------------------------------- beta endpoint classes

/-- The class of the `beta` row endpoint equals the `alpha` row endpoint class
of the same paired pair. -/
lemma rowEnd_beta (sr : O → R) (alpha beta : E → O) (e : E) :
    rowEnd sr alpha beta e = Quotient.mk'' (sr (beta e)) := by
  apply Quotient.sound'
  exact Relation.EqvGen.rel (sr (alpha e)) (sr (beta e))
    (⟨e, rfl, rfl⟩ : RowRel sr alpha beta (sr (alpha e)) (sr (beta e)))

/-- The class of the `beta` column endpoint equals the `alpha` column endpoint
class of the same paired pair. -/
lemma colEnd_beta (tg : O → C) (alpha beta : E → O) (e : E) :
    colEnd tg alpha beta e = Quotient.mk'' (tg (beta e)) := by
  apply Quotient.sound'
  exact Relation.EqvGen.rel (tg (alpha e)) (tg (beta e))
    (⟨e, rfl, rfl⟩ : ColRel tg alpha beta (tg (alpha e)) (tg (beta e)))

-- -------------------------------------------------- label equivalence

/-- An admissible row labeling is constant on `rowSetoid` classes. -/
lemma rowSetoid_rel_imp_eq_of_admissible (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (x : R → I) (y : C → J)
    (hA : Admissible sr tg alpha beta x y) :
    ∀ a b, (rowSetoid sr alpha beta).r a b → x a = x b := by
  intro a b hab
  induction hab with
  | rel x y h =>
      rcases h with ⟨e, ha, hb⟩
      rw [← ha, ← hb]
      exact (hA e).1
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- An admissible column labeling is constant on `colSetoid` classes. -/
lemma colSetoid_rel_imp_eq_of_admissible (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (x : R → I) (y : C → J)
    (hA : Admissible sr tg alpha beta x y) :
    ∀ a b, (colSetoid tg alpha beta).r a b → y a = y b := by
  intro a b hab
  induction hab with
  | rel x y h =>
      rcases h with ⟨e, ha, hb⟩
      rw [← ha, ← hb]
      exact (hA e).2
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- A pair of original labels is admissible iff the row labeling descends to
`rowSetoid` and the column labeling descends to `colSetoid`. -/
lemma admissible_iff_rowSetoid_le_ker_colSetoid_le_ker (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (x : R → I) (y : C → J) :
    Admissible sr tg alpha beta x y ↔
      rowSetoid sr alpha beta ≤ Setoid.ker x ∧ colSetoid tg alpha beta ≤ Setoid.ker y := by
  constructor
  · intro h
    constructor
    · apply Setoid.eqvGen_le
      intro a b hab
      rcases hab with ⟨e, ha, hb⟩
      rw [← ha, ← hb]
      exact (h e).1
    · apply Setoid.eqvGen_le
      intro a b hab
      rcases hab with ⟨e, ha, hb⟩
      rw [← ha, ← hb]
      exact (h e).2
  · intro h e
    constructor
    · exact h.1 (Relation.EqvGen.rel _ _ ⟨e, rfl, rfl⟩)
    · exact h.2 (Relation.EqvGen.rel _ _ ⟨e, rfl, rfl⟩)

/-- The exact quotient-label equivalence: quotient labels `(U → I) × (V → J)`
correspond bijectively to admissible original labels `{xy : (R → I) × (C → J) //
Admissible xy.1 xy.2}`, by pullback along `Quotient.mk''` and
`Quotient.liftOn'` respectively. -/
noncomputable def quotientLabelEquiv (sr : O → R) (tg : O → C)
    (alpha beta : E → O) :
    (RowQuotient sr alpha beta → I) × (ColQuotient tg alpha beta → J) ≃
      {xy : (R → I) × (C → J) // Admissible sr tg alpha beta xy.1 xy.2} where
  toFun fg :=
    ⟨(fg.1 ∘ Quotient.mk'', fg.2 ∘ Quotient.mk''), fun e =>
      ⟨congrArg fg.1 (rowEnd_beta sr alpha beta e),
        congrArg fg.2 (colEnd_beta tg alpha beta e)⟩⟩
  invFun xy :=
    ⟨(fun q => Quotient.liftOn' q xy.1.1
        (rowSetoid_rel_imp_eq_of_admissible sr tg alpha beta xy.1.1 xy.1.2 xy.2)),
      (fun q => Quotient.liftOn' q xy.1.2
        (colSetoid_rel_imp_eq_of_admissible sr tg alpha beta xy.1.1 xy.1.2 xy.2))⟩
  left_inv fg := by
    rcases fg with ⟨f, g⟩
    apply Prod.ext
    · funext q
      exact Quotient.inductionOn' q (fun r => by simp)
    · funext q
      exact Quotient.inductionOn' q (fun r => by simp)
  right_inv xy := by
    cases xy with
    | mk p hp =>
        apply Subtype.ext
        apply Prod.ext
        · funext r
          simp
        · funext r
          simp

/-- The quotient label equivalence sends `(f, g)` to the pullback pair
`(f ∘ Quotient.mk'', g ∘ Quotient.mk'')`. -/
lemma quotientLabelEquiv_apply (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (f : RowQuotient sr alpha beta → I)
    (g : ColQuotient tg alpha beta → J) :
    (quotientLabelEquiv sr tg alpha beta (f, g)).1 =
      (f ∘ Quotient.mk'', g ∘ Quotient.mk'') := by
  rfl

-- ------------------------------------------------------------- product and sums

/-- The product over paired pairs of the `w`-weights of the original labels at
the `alpha` endpoints. -/
noncomputable def pairWeight [Fintype E] (sr : O → R) (tg : O → C)
    (alpha : E → O) (w : I → J → ℝ) (x : R → I) (y : C → J) : ℝ :=
  ∏ e : E, w (x (sr (alpha e))) (y (tg (alpha e)))

/-- A sum over `α` of the indicator of `p` times `f` equals the sum of `f`
over the subtype of elements satisfying `p`. -/
private lemma sum_ite_eq_sum_subtype {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) :
    (∑ a : α, if p a then f a else 0) = ∑ a : {a : α // p a}, f a := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => if p a then f a else 0)]
  have h₁ : (∑ i : {x : α // p x}, (if p i.1 then f i.1 else 0)) =
      ∑ i : {x : α // p x}, f i.1 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact if_pos i.property
  have h₂ : (∑ i : {x : α // ¬ p x}, (if p i.1 then f i.1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg i.property
  rw [h₁, h₂, add_zero]

/-- Pulling back quotient labels to original labels replaces the weight by its
value at the endpoint classes. -/
lemma pairWeight_pullback [Fintype E] (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (w : I → J → ℝ) (f : RowQuotient sr alpha beta → I)
    (g : ColQuotient tg alpha beta → J) :
    pairWeight sr tg alpha w (f ∘ Quotient.mk'') (g ∘ Quotient.mk'') =
      ∏ e : E, w (f (rowEnd sr alpha beta e)) (g (colEnd tg alpha beta e)) := by
  simp [pairWeight, rowEnd, colEnd]

/-- The exact finite-sum identity: the sum over original labels of the product
of local indicators (which forces admissibility) equals the sum over quotient
labels of the product of `w`-weights at the endpoint classes. -/
theorem sum_prod_indicator_eq_sum_quotient
    (sr : O → R) (tg : O → C) (alpha beta : E → O)
    [Fintype R] [Fintype C] [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq R] [DecidableEq C] [DecidableEq I] [DecidableEq J]
    [Fintype (RowQuotient sr alpha beta)] [Fintype (ColQuotient tg alpha beta)]
    [DecidableEq (RowQuotient sr alpha beta)] [DecidableEq (ColQuotient tg alpha beta)]
    (w : I → J → ℝ) :
    (∑ x : R → I, ∑ y : C → J,
        ∏ e : E,
          if x (sr (alpha e)) = x (sr (beta e)) ∧
              y (tg (alpha e)) = y (tg (beta e))
            then w (x (sr (alpha e))) (y (tg (alpha e))) else 0)
    = (∑ f : RowQuotient sr alpha beta → I,
        ∑ g : ColQuotient tg alpha beta → J,
          ∏ e : E, w (f (rowEnd sr alpha beta e)) (g (colEnd tg alpha beta e))) := by
  classical
  calc
    (∑ x : R → I, ∑ y : C → J,
        ∏ e : E,
          if x (sr (alpha e)) = x (sr (beta e)) ∧
              y (tg (alpha e)) = y (tg (beta e))
            then w (x (sr (alpha e))) (y (tg (alpha e))) else 0)
        = ∑ x : R → I, ∑ y : C → J,
            if Admissible sr tg alpha beta x y
              then pairWeight sr tg alpha w x y else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hA : Admissible sr tg alpha beta x y
            · rw [if_pos hA]
              apply Finset.prod_congr rfl
              intro e he
              rw [if_pos (hA e)]
            · rw [if_neg hA]
              rcases not_forall.mp hA with ⟨e, he⟩
              apply Finset.prod_eq_zero (Finset.mem_univ e)
              exact if_neg he
    _ = ∑ xy : (R → I) × (C → J),
        if Admissible sr tg alpha beta xy.1 xy.2
          then pairWeight sr tg alpha w xy.1 xy.2 else 0 := by
        rw [← Fintype.sum_prod_type']
    _ = ∑ xy : {xy : (R → I) × (C → J) // Admissible sr tg alpha beta xy.1 xy.2},
        pairWeight sr tg alpha w xy.1.1 xy.1.2 := by
        rw [sum_ite_eq_sum_subtype (p := fun xy : (R → I) × (C → J) =>
          Admissible sr tg alpha beta xy.1 xy.2)
          (f := fun xy : (R → I) × (C → J) =>
            pairWeight sr tg alpha w xy.1 xy.2)]
    _ = (∑ fg : (RowQuotient sr alpha beta → I) × (ColQuotient tg alpha beta → J),
        ∏ e : E, w (fg.1 (rowEnd sr alpha beta e)) (fg.2 (colEnd tg alpha beta e))) := by
        rw [(Equiv.sum_comp (e := quotientLabelEquiv sr tg alpha beta)
          (g := fun xy => pairWeight sr tg alpha w xy.1.1 xy.1.2)).symm]
        apply Finset.sum_congr rfl
        intro fg hfg
        rcases fg with ⟨f, g⟩
        rw [quotientLabelEquiv_apply]
        exact pairWeight_pullback sr tg alpha beta w f g
    _ = (∑ f : RowQuotient sr alpha beta → I,
        ∑ g : ColQuotient tg alpha beta → J,
          ∏ e : E, w (f (rowEnd sr alpha beta e)) (g (colEnd tg alpha beta e))) := by
        rw [Fintype.sum_prod_type]

-- ------------------------------------------------------------- graph transfer

/-- The map on vertices induced by quotienting rows and columns is a surjective
graph homomorphism from the original occurrence graph to the paired quotient
occurrence graph.  The endpoint coverage bijection is used to realize every
original occurrence `o` by the paired pair whose `alpha`- or `beta`-endpoint is
`o`; when `o` is a `beta` endpoint, `rowEnd_beta` / `colEnd_beta` identify the
quotient classes. -/
def quotientGraphHom (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (hcover : Function.Bijective (Sum.elim alpha beta)) :
    SimpleGraph.bipartiteOccurrenceGraph sr tg →g
      SimpleGraph.bipartiteOccurrenceGraph (rowEnd sr alpha beta) (colEnd tg alpha beta) where
  toFun := Sum.map (Quotient.mk'' : R → RowQuotient sr alpha beta)
    (Quotient.mk'' : C → ColQuotient tg alpha beta)
  map_rel' := by
    intro a b hab
    rcases hab with ⟨u, v, hcase, he⟩
    refine ⟨Quotient.mk'' u, Quotient.mk'' v, ?_, ?_⟩
    · rcases hcase with h | h
      · exact Or.inl ⟨by simp [h.1], by simp [h.2]⟩
      · exact Or.inr ⟨by simp [h.1], by simp [h.2]⟩
    · rcases he with ⟨o, ho1, ho2⟩
      have hpre : ∃ e : E ⊕ E, Sum.elim alpha beta e = o := hcover.2 o
      rcases hpre with ⟨e, heo⟩
      cases e with
      | inl e =>
          refine ⟨e, ?_, ?_⟩
          · change alpha e = o at heo
            have hs : sr (alpha e) = u := by
              rw [← ho1, heo]
            rw [rowEnd, hs]
          · change alpha e = o at heo
            have ht : tg (alpha e) = v := by
              rw [← ho2, heo]
            rw [colEnd, ht]
      | inr e =>
          refine ⟨e, ?_, ?_⟩
          · change beta e = o at heo
            have hs : sr (beta e) = u := by
              rw [← ho1, heo]
            rw [rowEnd_beta, hs]
          · change beta e = o at heo
            have ht : tg (beta e) = v := by
              rw [← ho2, heo]
            rw [colEnd_beta, ht]

/-- The vertex map of `quotientGraphHom` is surjective:
every quotient vertex has a representative. -/
lemma surjective_sum_map_quotient (sr : O → R) (tg : O → C)
    (alpha beta : E → O) :
    Function.Surjective (Sum.map (Quotient.mk'' : R → RowQuotient sr alpha beta)
      (Quotient.mk'' : C → ColQuotient tg alpha beta)) := by
  intro x
  cases x with
  | inl q =>
      obtain ⟨r, hr⟩ := Quotient.exists_rep q
      refine ⟨Sum.inl r, ?_⟩
      simp [hr]
  | inr q =>
      obtain ⟨c, hc⟩ := Quotient.exists_rep q
      refine ⟨Sum.inr c, ?_⟩
      simp [hc]

/-- Connectedness of the original occurrence graph transfers to the paired
quotient occurrence graph along the surjective homomorphism. -/
theorem connected_quotient_of_connected (sr : O → R) (tg : O → C)
    (alpha beta : E → O) (hcover : Function.Bijective (Sum.elim alpha beta))
    (hG : (SimpleGraph.bipartiteOccurrenceGraph sr tg).Connected) :
    (SimpleGraph.bipartiteOccurrenceGraph (rowEnd sr alpha beta) (colEnd tg alpha beta)).Connected := by
  exact SimpleGraph.Connected.map
    (quotientGraphHom sr tg alpha beta hcover)
    (surjective_sum_map_quotient sr tg alpha beta) hG

-- ----------------------------------------------- the alternating Gram cycle

/-- The row endpoint map of the alternating Gram cycle of dimension `p`:
`Sum.inl t ↦ t` (a `row t -- col t` occurrence) and
`Sum.inr t ↦ finRotate p t` (a `row (finRotate p t) -- col t` occurrence). -/
def cycleRow (p : ℕ) : Fin p ⊕ Fin p → Fin p
  | Sum.inl t => t
  | Sum.inr t => finRotate p t

/-- The column endpoint map of the alternating Gram cycle of dimension `p`:
every occurrence `Sum.inl t` and `Sum.inr t` sits in column `t`. -/
def cycleCol (p : ℕ) : Fin p ⊕ Fin p → Fin p
  | Sum.inl t => t
  | Sum.inr t => t

/-- In the Gram-cycle occurrence graph, row `t` is adjacent to column `t`
via the occurrence `Sum.inl t`. -/
lemma cycle_inl_edge (p : ℕ) (x : Fin p) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow p) (cycleCol p)).Adj
      (Sum.inl x) (Sum.inr x) := by
  refine ⟨x, x, Or.inl ⟨rfl, rfl⟩, ?_⟩
  refine ⟨Sum.inl x, ?_, ?_⟩ <;> rfl

/-- In the Gram-cycle occurrence graph, column `t` is adjacent to row
`finRotate p t` via the occurrence `Sum.inr t`. -/
lemma cycle_inr_edge (p : ℕ) (x : Fin p) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow p) (cycleCol p)).Adj
      (Sum.inr x) (Sum.inl (finRotate p x)) := by
  refine ⟨finRotate p x, x, Or.inr ⟨rfl, rfl⟩, ?_⟩
  refine ⟨Sum.inr x, ?_, ?_⟩ <;> rfl

/-- Iterating the two-edge steps `row s -- col s -- row (finRotate p s)`,
every row of the Gram-cycle occurrence graph is reachable from row `0` (the
walk runs backwards from row `t` towards row `0`). -/
lemma cycle_reachable_row_down (q : ℕ) (m : ℕ) (hm : m < q + 1) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Reachable
      (Sum.inl (⟨m, hm⟩ : Fin (q + 1))) (Sum.inl (0 : Fin (q + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m < q + 1 := Nat.lt_of_succ_lt hm
      have hstep : finRotate (q + 1) (⟨m, hm'⟩ : Fin (q + 1)) = ⟨m + 1, hm⟩ := by
        simpa using finRotate_of_lt (n := q) (k := m) (by omega)
      have hroad :
          (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Reachable
            (Sum.inl (⟨m, hm'⟩ : Fin (q + 1)))
            (Sum.inl (⟨m + 1, hm⟩ : Fin (q + 1))) := by
        simpa [hstep] using
          ((cycle_inl_edge (q + 1) (⟨m, hm'⟩ : Fin (q + 1))).reachable.trans
            (cycle_inr_edge (q + 1) (⟨m, hm'⟩ : Fin (q + 1))).reachable)
      exact (hroad.symm).trans (ih hm')

/-- Every row of the Gram-cycle occurrence graph is reachable from row `0`. -/
lemma cycle_reachable_row (q : ℕ) (t : Fin (q + 1)) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Reachable
      (Sum.inl (0 : Fin (q + 1))) (Sum.inl t) := by
  exact (cycle_reachable_row_down q t.val t.isLt).symm

/-- Every column of the Gram-cycle occurrence graph is reachable from row `0`
through `row t -- col t`. -/
lemma cycle_reachable_col (q : ℕ) (c : Fin (q + 1)) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Reachable
      (Sum.inl (0 : Fin (q + 1))) (Sum.inr c) := by
  exact (cycle_reachable_row q c).trans (cycle_inl_edge (q + 1) c).reachable

/-- Every vertex of the Gram-cycle occurrence graph is reachable from row `0`. -/
lemma cycle_reachable_zero (q : ℕ) :
    ∀ x : Sum (Fin (q + 1)) (Fin (q + 1)),
      (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Reachable
        (Sum.inl (0 : Fin (q + 1))) x := by
  intro x
  cases x with
  | inl r => exact cycle_reachable_row q r
  | inr c => exact cycle_reachable_col q c

/-- The occurrence graph of the alternating Gram cycle of dimension `q + 1`
is connected.  This proves the fact from the explicit closed-walk structure
(`row t -- col t -- row (finRotate p t)`) and does not assume any quotient
connectedness or spanning-tree certificate. -/
theorem bipartiteOccurrenceGraph_cycle_connected (q : ℕ) :
    (SimpleGraph.bipartiteOccurrenceGraph (cycleRow (q + 1)) (cycleCol (q + 1))).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl (0 : Fin (q + 1)), ?_⟩
  intro x
  exact cycle_reachable_zero q x

/-- The row quotient of the Gram cycle is nonempty (class of row `0`). -/
lemma rowQuotient_nonempty_cycle (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Nonempty (RowQuotient (cycleRow (q + 1)) alpha beta) :=
  ⟨Quotient.mk'' (0 : Fin (q + 1))⟩

/-- The column quotient of the Gram cycle is nonempty (class of column `0`). -/
lemma colQuotient_nonempty_cycle (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Nonempty (ColQuotient (cycleCol (q + 1)) alpha beta) :=
  ⟨Quotient.mk'' (0 : Fin (q + 1))⟩

/-- For the alternating Gram cycle of dimension `q + 1`, every endpoint pairing
whose `alpha`/`beta` endpoints cover the original occurrences exactly once has
a connected paired quotient graph. -/
theorem bipartiteOccurrenceGraph_quotient_cycle_connected (q : ℕ) [Fintype E]
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (hcover : Function.Bijective (Sum.elim alpha beta)) :
    (SimpleGraph.bipartiteOccurrenceGraph
        (rowEnd (cycleRow (q + 1)) alpha beta)
        (colEnd (cycleCol (q + 1)) alpha beta)).Connected := by
  exact SimpleGraph.Connected.map
    (quotientGraphHom (cycleRow (q + 1)) (cycleCol (q + 1))
      alpha beta hcover)
    (surjective_sum_map_quotient (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta)
    (bipartiteOccurrenceGraph_cycle_connected q)

/-- The number of paired pairs equals the cycle dimension `q + 1`: this follows
from the bijection `E ⊕ E ≃ Fin (q + 1) ⊕ Fin (q + 1)` by finite-cardinality
arithmetic (no quotient cardinality formula is used). -/
lemma card_pairing_eq_succ (q : ℕ) [Fintype E]
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (hcover : Function.Bijective (Sum.elim alpha beta)) :
    Fintype.card E = q + 1 := by
  have hsum : Fintype.card (E ⊕ E) = 2 * Fintype.card E := by
    rw [Fintype.card_sum]
    ring
  have hsum' : Fintype.card (Fin (q + 1) ⊕ Fin (q + 1)) = 2 * (q + 1) := by
    rw [Fintype.card_sum]
    simp only [Fintype.card_fin]
    omega
  have hc : Fintype.card (E ⊕ E) = Fintype.card (Fin (q + 1) ⊕ Fin (q + 1)) :=
    Fintype.card_congr (Equiv.ofBijective (Sum.elim alpha beta) hcover)
  have h2 : 2 * Fintype.card E = 2 * (q + 1) := by
    rw [← hsum, hc, hsum']
  omega

end NLAlib.PairingQuotient

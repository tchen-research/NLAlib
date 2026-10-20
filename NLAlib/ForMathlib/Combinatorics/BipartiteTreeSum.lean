import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.SuccPred
import NLAlib.ForMathlib.Combinatorics.BipartiteLeafSum

open scoped BigOperators
open Finset

/-!
# Bipartite partition-sum bound for row-rooted trees

This file formalizes the partition-sum bound for every tree constructible by the
finite row-rooted syntax below. It supplies the tree estimate in the
leaf-elimination argument supporting the atlas card
`independent-entry-gaussian-extremum`.

A row-rooted bipartite tree with `r` non-root rows and `q` columns is built by the
indexed syntax `RowRootedBipartiteTree r q`:

* `root : RowRootedBipartiteTree 0 0` starts from the root row alone;
* `addRow t v` attaches a new row leaf (index `0`) to the existing column `v`,
  shifting all old row indices by `Fin.succ`;
* `addColumn t u` attaches a new column leaf (index `0`) to the existing row `u`,
  shifting all old column indices by `Fin.succ`.

Rows are indexed by `Fin (r+1)` and columns by `Fin q`. The original root starts
at row index `0` and shifts whenever a new row is inserted; it is not the new
vertex at index `0` after an `addRow` step.
The actual edge list is defined recursively, and the partition sum is the sum over
all labelings `x : Fin (r+1) → I`, `y : Fin q → J` of the product of `w (x i) (y j)`
over the edges.

The main result `partitionSum_le` says that if `w` is nonnegative, every column sum
is at most `a`, and every row sum is at most `c`, then

```
partitionSum t w ≤ (Fintype.card I : ℝ) * a ^ r * c ^ q
```

for every constructible tree `t : RowRootedBipartiteTree r q`. The proof eliminates leaves one at
a time (`partitionSum_addRow_le`, `partitionSum_addColumn_le`) using the leaf-kernel
estimates `sum_row_leaf_mul_le_mul_sum` / `sum_column_leaf_mul_le_mul_sum`, after proving the
recursive weight identities that connect the concrete edge list of a grown tree to
that of the original tree. Only the root row label remains free, giving the factor
`Fintype.card I`.

The spanning-tree bridge from arbitrary finite connected bipartite multigraphs
with a nonempty row vertex type is proved in `BipartiteSpanningTree`.
The resulting graph bound, combining this tree estimate with the off-tree
entry cap, is proved in `BipartitePartitionBound`.
-/

noncomputable section
namespace NLAlib

variable {r q : ℕ}

/-- Syntax for constructing row-rooted bipartite trees with `r` non-root rows and
`q` columns. Row vertices are indexed by `Fin (r+1)` and column vertices by
`Fin q`. A new row is inserted at index `0`, shifting all earlier row vertices,
including the original root. -/
inductive RowRootedBipartiteTree : ℕ → ℕ → Type
  | root : RowRootedBipartiteTree 0 0
  | addRow : {r q : ℕ} → RowRootedBipartiteTree r q → Fin q →
      RowRootedBipartiteTree (r+1) q
  | addColumn : {r q : ℕ} → RowRootedBipartiteTree r q → Fin (r+1) →
      RowRootedBipartiteTree r (q+1)

namespace RowRootedBipartiteTree

/-- The actual edge list of the tree: the list of row-column index pairs, built
by successive leaf attachment. `addRow` attaches the edge `(0, v)` (the new row leaf, index `0`, made
adjacent to column `v`) and shifts old row endpoints by `Fin.succ`; `addColumn`
attaches `(u, 0)` and shifts old column endpoints by `Fin.succ`. -/
def edgeList {r q : ℕ} : RowRootedBipartiteTree r q → List (Fin (r+1) × Fin q)
  | root => []
  | addRow t v => (0, v) :: (edgeList t).map (fun e => (Fin.succ e.1, e.2))
  | addColumn t u => (u, 0) :: (edgeList t).map (fun e => (e.1, Fin.succ e.2))

/-- The edge list of a tree with a new row leaf starts with the new edge `(0, v)`
and then contains the old edges with row indices shifted by `Fin.succ`. -/
lemma edgeList_addRow {r q : ℕ} (t : RowRootedBipartiteTree r q) (v : Fin q) :
    edgeList (addRow t v) =
      (0, v) :: (edgeList t).map (fun e => (Fin.succ e.1, e.2)) := by
  rfl

/-- The edge list of a tree with a new column leaf starts with the new edge
`(u, 0)` and then contains the old edges with column indices shifted by
`Fin.succ`. -/
lemma edgeList_addColumn {r q : ℕ} (t : RowRootedBipartiteTree r q) (u : Fin (r+1)) :
    edgeList (addColumn t u) =
      (u, 0) :: (edgeList t).map (fun e => (e.1, Fin.succ e.2)) := by
  rfl

variable {I J : Type*}

/-- Weight of the tree under labelings `x` of rows and `y` of columns: the product
of `w (x i) (y j)` over all edges `(i, j)` of the tree. -/
def weight (w : I → J → ℝ) {r q : ℕ} (t : RowRootedBipartiteTree r q)
    (x : Fin (r+1) → I) (y : Fin q → J) : ℝ :=
  ((edgeList t).map (fun e => w (x e.1) (y e.2))).prod

/-- Nonnegativity of the tree weight when `w` is nonnegative. -/
theorem weight_nonneg (w : I → J → ℝ) {r q : ℕ} (t : RowRootedBipartiteTree r q)
    (hwnn : ∀ i j, 0 ≤ w i j) (x : Fin (r+1) → I) (y : Fin q → J) :
    0 ≤ weight w t x y := by
  unfold weight
  exact List.prod_nonneg
    (s := (edgeList t).map (fun e => w (x e.1) (y e.2)))
    (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨e, he, rfl⟩
      exact hwnn (x e.1) (y e.2))

/-- The recursive weight identity for a new row leaf: the weight of `addRow t v`
factorizes as the weight of the new edge `(0, v)` times the weight of the original
tree with row indices shifted by `Fin.succ`. -/
theorem weight_addRow_eq (t : RowRootedBipartiteTree r q) (v : Fin q)
    (w : I → J → ℝ) (x : Fin ((r+1)+1) → I) (y : Fin q → J) :
    weight w (addRow t v) x y =
      w (x 0) (y v) * weight w t (fun i => x (Fin.succ i)) y := by
  unfold weight
  rw [edgeList_addRow]
  rw [List.map_cons, List.prod_cons]
  congr 1
  rw [List.map_map]
  rfl

/-- The recursive weight identity for a new column leaf: the weight of
`addColumn t u` factorizes as the weight of the new edge `(u, 0)` times the weight
of the original tree with column indices shifted by `Fin.succ`. -/
theorem weight_addColumn_eq (t : RowRootedBipartiteTree r q) (u : Fin (r+1))
    (w : I → J → ℝ) (x : Fin (r+1) → I) (y : Fin (q+1) → J) :
    weight w (addColumn t u) x y =
      w (x u) (y 0) * weight w t x (fun j => y (Fin.succ j)) := by
  unfold weight
  rw [edgeList_addColumn]
  rw [List.map_cons, List.prod_cons]
  congr 1
  rw [List.map_map]
  rfl

variable [Fintype I] [Fintype J]

/-- Sum of the tree weight over all labelings of rows (`Fin (r+1)`, including the
root row) and of columns. -/
def partitionSum {r q : ℕ} (t : RowRootedBipartiteTree r q) (w : I → J → ℝ) : ℝ :=
  ∑ x : Fin (r+1) → I, ∑ y : Fin q → J, weight w t x y

/-- The equivalence `Fin (n+1) ≃ Option (Fin n)` extended to functions: a labeling
of the rows of a tree with one more row is the same data as a labeling of
`Option (Fin n)`, where `none` is the new row and `some i` is the shifted row `i`. -/
private def optionPiEquiv {α : Type*} (n : ℕ) :
    (Fin (n+1) → α) ≃ (Option (Fin n) → α) :=
  { toFun := fun g o => g ((finSuccEquiv n).symm o)
    invFun := fun g i => g (finSuccEquiv n i)
    left_inv := by
      intro g
      funext i
      simp
    right_inv := by
      intro g
      funext o
      simp }

private lemma optionPiEquiv_apply_none {α : Type*} (n : ℕ) (x : Fin (n+1) → α) :
    (optionPiEquiv n x) none = x 0 := by
  simp [optionPiEquiv]

private lemma optionPiEquiv_apply_some {α : Type*} (n : ℕ) (x : Fin (n+1) → α)
    (i : Fin n) :
    (optionPiEquiv n x) (some i) = x (Fin.succ i) := by
  simp [optionPiEquiv]

/-- Reindexing a row sum through `optionPiEquiv`: summing over labelings of
`Fin (n+1)` weighted by the value of the `Option (Fin n)`-labeling equals summing
over `Option (Fin n)`-labelings directly. -/
private lemma sum_optionPiEquiv {I J : Type*} [Fintype I] [Fintype J]
    {n q : ℕ}
    (F : (Option (Fin n) → I) → (Fin q → J) → ℝ) :
    (∑ x : Fin (n+1) → I, ∑ y : Fin q → J,
        F (optionPiEquiv n x) y) =
      ∑ x : Option (Fin n) → I, ∑ y : Fin q → J, F x y := by
  exact Equiv.sum_comp (optionPiEquiv (α := I) n)
    (g := fun x' => ∑ y : Fin q → J, F x' y)

/-- The size of the edge list is `r + q`: each of the `r` non-root rows and `q`
columns is attached exactly once. -/
theorem edgeList_length (t : RowRootedBipartiteTree r q) :
    (edgeList t).length = r + q := by
  induction t with
  | root => simp [edgeList]
  | addRow t v ih =>
      simp [edgeList, List.length_map, ih]
      ac_rfl
  | addColumn t u ih =>
      simp [edgeList, List.length_map, ih]
      ac_rfl

/-- The edge list contains no repeated edge. -/
theorem edgeList_nodup (t : RowRootedBipartiteTree r q) :
    (edgeList t).Nodup := by
  induction t with
  | root => simp [edgeList]
  | addRow t v ih =>
      simp only [edgeList]
      refine List.Nodup.cons ?_ ?_
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨e, he, heeq⟩
        have hzero : Fin.succ e.1 = 0 := congrArg Prod.fst heeq
        exact (Fin.succ_ne_zero e.1) hzero
      · refine List.Nodup.map ?_ ih
        intro a b h
        rcases Prod.ext_iff.mp h with ⟨h1, h2⟩
        exact Prod.ext (Fin.succ_injective _ h1) h2
  | addColumn t u ih =>
      simp only [edgeList]
      refine List.Nodup.cons ?_ ?_
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨e, he, heeq⟩
        have hzero : Fin.succ e.2 = 0 := congrArg Prod.snd heeq
        exact (Fin.succ_ne_zero e.2) hzero
      · refine List.Nodup.map ?_ ih
        intro a b h
        rcases Prod.ext_iff.mp h with ⟨h1, h2⟩
        exact Prod.ext h1 (Fin.succ_injective _ h2)

/-- Row-leaf elimination identity: summing the weight of `addRow t v` over the label
of the new row equals summing the column sum `∑ i, w i (y v)` of the original tree
weight. This is the semantic bridge between the concrete partition sum of a grown
tree and the partition sum of the original tree. -/
theorem partitionSum_addRow_eq (t : RowRootedBipartiteTree r q) (v : Fin q)
    (w : I → J → ℝ) :
    partitionSum (addRow t v) w =
      ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
        (∑ i : I, w i (y v)) * weight w t x y := by
  calc
    partitionSum (addRow t v) w
        = ∑ x : Fin ((r+1)+1) → I, ∑ y : Fin q → J,
            w (x 0) (y v) * weight w t (fun i => x (Fin.succ i)) y := by
          simp [partitionSum, weight_addRow_eq]
    _ = ∑ x : Option (Fin (r+1)) → I, ∑ y : Fin q → J,
            w (x none) (y v) * weight w t (fun i => x (some i)) y := by
          let F : (Option (Fin (r+1)) → I) → (Fin q → J) → ℝ :=
            fun x' y => w (x' none) (y v) * weight w t (fun i => x' (some i)) y
          calc
            (∑ x : Fin ((r+1)+1) → I, ∑ y : Fin q → J,
                w (x 0) (y v) * weight w t (fun i => x (Fin.succ i)) y)
                = ∑ x : Fin ((r+1)+1) → I, ∑ y : Fin q → J,
                    F (optionPiEquiv (r+1) x) y := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  simp [F, optionPiEquiv_apply_none, optionPiEquiv_apply_some]
            _ = ∑ x : Option (Fin (r+1)) → I, ∑ y : Fin q → J, F x y := by
                  exact sum_optionPiEquiv (n := r+1) F
    _ = ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
            (∑ i : I, w i (y v)) * weight w t x y := by
          exact sum_row_leaf_mul_eq_sum_column_sum_mul (U := Fin (r+1)) (V := Fin q)
            (I := I) (J := J) (v := v) (w := w)
            (F := fun x' y => weight w t x' y)

/-- Column-leaf elimination identity: summing the weight of `addColumn t u` over
the label of the new column equals summing the row sum `∑ j, w (x u) j` of the
original tree weight. -/
theorem partitionSum_addColumn_eq (t : RowRootedBipartiteTree r q) (u : Fin (r+1))
    (w : I → J → ℝ) :
    partitionSum (addColumn t u) w =
      ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
        (∑ j : J, w (x u) j) * weight w t x y := by
  calc
    partitionSum (addColumn t u) w
        = ∑ x : Fin (r+1) → I, ∑ y : Fin (q+1) → J,
            w (x u) (y 0) * weight w t x (fun j => y (Fin.succ j)) := by
          simp [partitionSum, weight_addColumn_eq]
    _ = ∑ x : Fin (r+1) → I, ∑ y : Fin (q+1) → J,
            w (x u) ((optionPiEquiv q y) none) *
              weight w t x (fun j => (optionPiEquiv q y) (some j)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp [optionPiEquiv_apply_none, optionPiEquiv_apply_some]
    _ = ∑ x : Fin (r+1) → I, ∑ y : Option (Fin q) → J,
            w (x u) (y none) * weight w t x (fun j => y (some j)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact Equiv.sum_comp (optionPiEquiv (α := J) q)
            (g := fun y' : Option (Fin q) → J =>
              w (x u) (y' none) * weight w t x (fun j => y' (some j)))
    _ = ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
            (∑ j : J, w (x u) j) * weight w t x y := by
          exact sum_column_leaf_mul_eq_sum_row_sum_mul (U := Fin (r+1)) (V := Fin q)
            (I := I) (J := J) (u := u) (w := w)
            (F := fun x y => weight w t x y)

/-- Adding a row leaf costs at most the column-sum factor `a`. -/
theorem partitionSum_addRow_le (t : RowRootedBipartiteTree r q) (v : Fin q)
    (w : I → J → ℝ) (a : ℝ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a) :
    partitionSum (addRow t v) w ≤ a * partitionSum t w := by
  rw [partitionSum_addRow_eq t v w]
  calc
    (∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
        (∑ i : I, w i (y v)) * weight w t x y)
        ≤ ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
            a * weight w t x y := by
          refine Finset.sum_le_sum ?_
          intro x hx
          refine Finset.sum_le_sum ?_
          intro y hy
          exact mul_le_mul_of_nonneg_right (hcol (y v)) (weight_nonneg w t hwnn x y)
    _ = a * partitionSum t w := by
          simp [partitionSum, Finset.mul_sum]

/-- Adding a column leaf costs at most the row-sum factor `c`. -/
theorem partitionSum_addColumn_le (t : RowRootedBipartiteTree r q) (u : Fin (r+1))
    (w : I → J → ℝ) (c : ℝ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ c) :
    partitionSum (addColumn t u) w ≤ c * partitionSum t w := by
  rw [partitionSum_addColumn_eq t u w]
  calc
    (∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
        (∑ j : J, w (x u) j) * weight w t x y)
        ≤ ∑ x : Fin (r+1) → I, ∑ y : Fin q → J,
            c * weight w t x y := by
          refine Finset.sum_le_sum ?_
          intro x hx
          refine Finset.sum_le_sum ?_
          intro y hy
          exact mul_le_mul_of_nonneg_right (hrow (x u)) (weight_nonneg w t hwnn x y)
    _ = c * partitionSum t w := by
          simp [partitionSum, Finset.mul_sum]

/-- Bound for every tree constructed by `RowRootedBipartiteTree`: if `w` is
nonnegative, every column sum of `w` is at most `a`, and every row sum of `w` is
at most `c`, then the partition sum is at most `Fintype.card I * a ^ r * c ^ q`.
Only the root-row label remains free after eliminating all leaf labels, which gives
the `Fintype.card I` factor. -/
theorem partitionSum_le (t : RowRootedBipartiteTree r q)
    (w : I → J → ℝ) (a c : ℝ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ c)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    partitionSum t w ≤ (Fintype.card I : ℝ) * a ^ r * c ^ q := by
  refine RowRootedBipartiteTree.rec
    (motive := fun r q t => partitionSum t w ≤ (Fintype.card I : ℝ) * a ^ r * c ^ q)
    ?_ ?_ ?_ t
  · simp [partitionSum, weight, edgeList]
  · intro r q t v ih
    calc
      partitionSum (addRow t v) w ≤ a * partitionSum t w :=
        partitionSum_addRow_le t v w a hwnn hcol
      _ ≤ a * ((Fintype.card I : ℝ) * a ^ r * c ^ q) := by
        exact mul_le_mul_of_nonneg_left ih ha
      _ = (Fintype.card I : ℝ) * a ^ (r+1) * c ^ q := by
        rw [pow_succ']
        ring
  · intro r q t u ih
    calc
      partitionSum (addColumn t u) w ≤ c * partitionSum t w :=
        partitionSum_addColumn_le t u w c hwnn hrow
      _ ≤ c * ((Fintype.card I : ℝ) * a ^ r * c ^ q) := by
        exact mul_le_mul_of_nonneg_left ih hc
      _ = (Fintype.card I : ℝ) * a ^ r * c ^ (q+1) := by
        rw [pow_succ']
        ring

end RowRootedBipartiteTree
end NLAlib

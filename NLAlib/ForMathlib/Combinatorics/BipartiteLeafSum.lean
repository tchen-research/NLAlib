import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs

open scoped BigOperators
open Finset

/-!
# Bipartite leaf elimination

This file contains the finite algebra behind the leaf-elimination step of the
bipartite partition-sum bound used by the atlas card
`independent-entry-gaussian-extremum`.
No graph or probability library is needed here: the statements are pure finite
algebra over `ℝ` with arbitrary labelings.

The central identity reindexes a sum over labelings of `Option U` (a row set with
one distinguished leaf attached) by the label of the new leaf and the labeling of
the remaining vertices:

```
∑ x : Option U → I, ∑ y : V → J, w (x none) (y v) * F (fun u => x (some u)) y
  = ∑ x : U → I, ∑ y : V → J, (∑ i : I, w i (y v)) * F x y
```

Under `F ≥ 0` and the column cap `∀ j, ∑ i, w i j ≤ a`, this gives the per-leaf
estimate

```
∑ x : Option U → I, ∑ y : V → J, w (x none) (y v) * F (fun u => x (some u)) y
  ≤ a * ∑ x : U → I, ∑ y : V → J, F x y
```

`sum_column_leaf_mul_eq_sum_row_sum_mul` / `sum_column_leaf_mul_le_mul_sum` are the column-leaf
variants, derived from the same generic algebra by swapping the roles of rows and
columns rather than re-proving the identity.

We also provide the occurrence regrouping bridge `Fintype.prod_fiber_pow` for an
indexed family of edge occurrences `idx : R → E`:

```
∏ r : R, z (idx r) = ∏ e : E, z e ^ ((univ.filter (fun r => idx r = e)).card)
```

and the off-tree factor cap `prod_bipartite_edge_weight_le_pow` used to remove the
factors on non-tree edges before leaf elimination. These are prerequisite kernels
for the extremum proof; they do not by themselves complete the atlas card.
-/

namespace Fintype

/-- Occurrence regrouping bridge: the product over occurrences of a function
`z` of the occurrence kind equals the product over kinds of `z e` raised to the
number of occurrences of kind `e`. -/
theorem prod_fiber_pow {R E : Type*} [Fintype R] [DecidableEq E] [Fintype E]
    (idx : R → E) (z : E → ℝ) :
    (∏ r : R, z (idx r)) =
      ∏ e : E, z e ^ ((univ : Finset R).filter (fun r => idx r = e)).card := by
  calc
    (∏ r : R, z (idx r)) = ∏ e : E, ∏ _r : {r : R // idx r = e}, z e := by
      exact (Fintype.prod_fiberwise' idx z).symm
    _ = ∏ e : E, z e ^ ((univ : Finset R).filter (fun r => idx r = e)).card := by
      refine Finset.prod_congr rfl ?_
      intro e he
      rw [← Fintype.card_subtype (p := fun r : R => idx r = e)]
      simp

end Fintype

noncomputable section
namespace NLAlib

variable {U V I J : Type*} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq U] [DecidableEq V]

/-- Summing over labelings of `Option U` (a row set with one new leaf attached)
equals summing over the label of the new leaf and the labelings of `U`, with the
leaf factor `w (x none) (y v)` extracted from `F`. This is the row-leaf
elimination identity of the bipartite partition-sum argument; it holds with no
sign assumption and for empty index types. -/
theorem sum_row_leaf_mul_eq_sum_column_sum_mul (v : V) (w : I → J → ℝ)
    (F : (U → I) → (V → J) → ℝ) :
    (∑ x : Option U → I, ∑ y : V → J,
        w (x none) (y v) * F (fun u => x (some u)) y) =
      ∑ x : U → I, ∑ y : V → J, (∑ i : I, w i (y v)) * F x y := by
  let e : (Option U → I) ≃ I × (U → I) :=
    Equiv.piOptionEquivProd (α := U) (β := fun _ : Option U => I)
  calc
    (∑ x : Option U → I, ∑ y : V → J,
        w (x none) (y v) * F (fun u => x (some u)) y)
        = ∑ p : I × (U → I), ∑ y : V → J, w p.1 (y v) * F p.2 y := by
          exact (Equiv.sum_comp e (g := fun p : I × (U → I) =>
            ∑ y : V → J, w p.1 (y v) * F p.2 y))
    _ = ∑ x : U → I, ∑ i : I, ∑ y : V → J,
          w i (y v) * F x y := by
          exact Fintype.sum_prod_type_right (f := fun p : I × (U → I) =>
            ∑ y : V → J, w p.1 (y v) * F p.2 y)
    _ = ∑ x : U → I, ∑ y : V → J, ∑ i : I,
          w i (y v) * F x y := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact Finset.sum_comm (s := (Finset.univ : Finset I))
            (t := (Finset.univ : Finset (V → J)))
            (f := fun (i : I) (y : V → J) => w i (y v) * F x y)
    _ = ∑ x : U → I, ∑ y : V → J, (∑ i : I, w i (y v)) * F x y := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          exact (Finset.sum_mul (s := (Finset.univ : Finset I))
            (f := fun i : I => w i (y v)) (a := F x y)).symm

/-- Row-leaf elimination estimate: if `F` is nonnegative and every column sum of
`w` is at most `a`, then summing over the label of the new leaf costs at most the
factor `a`. -/
theorem sum_row_leaf_mul_le_mul_sum (v : V) (a : ℝ) (w : I → J → ℝ)
    (F : (U → I) → (V → J) → ℝ)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a)
    (hF : ∀ (x : U → I) (y : V → J), 0 ≤ F x y) :
    (∑ x : Option U → I, ∑ y : V → J,
        w (x none) (y v) * F (fun u => x (some u)) y) ≤
      a * (∑ x : U → I, ∑ y : V → J, F x y) := by
  rw [sum_row_leaf_mul_eq_sum_column_sum_mul v w F]
  calc
    (∑ x : U → I, ∑ y : V → J, (∑ i : I, w i (y v)) * F x y)
        ≤ ∑ x : U → I, ∑ y : V → J, a * F x y := by
          refine Finset.sum_le_sum ?_
          intro x hx
          refine Finset.sum_le_sum ?_
          intro y hy
          exact mul_le_mul_of_nonneg_right (hcol (y v)) (hF x y)
    _ = ∑ x : U → I, a * (∑ y : V → J, F x y) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact (Finset.mul_sum (s := (Finset.univ : Finset (V → J)))
            (f := fun y : V → J => F x y) (a := a)).symm
    _ = a * (∑ x : U → I, ∑ y : V → J, F x y) := by
          exact (Finset.mul_sum (s := (Finset.univ : Finset (U → I)))
            (f := fun x : U → I => ∑ y : V → J, F x y) (a := a)).symm

/-- Column-leaf analogue of `sum_row_leaf_mul_eq_sum_column_sum_mul`: the new leaf is a column
(`Option V`) whose label is summed out, leaving the row sum `∑ j, w (x u) j`.
Derived from the row identity by swapping the roles of rows (`U`, `I`) and
columns (`V`, `J`) and flipping `w`. -/
theorem sum_column_leaf_mul_eq_sum_row_sum_mul (u : U) (w : I → J → ℝ)
    (F : (U → I) → (V → J) → ℝ) :
    (∑ x : U → I, ∑ y : Option V → J,
        w (x u) (y none) * F x (fun v => y (some v))) =
      ∑ x : U → I, ∑ y : V → J, (∑ j : J, w (x u) j) * F x y := by
  have h := sum_row_leaf_mul_eq_sum_column_sum_mul (U := V) (V := U) (I := J) (J := I)
    (v := u) (w := fun j i => w i j) (F := fun y x => F x y)
  rw [Finset.sum_comm (s := (Finset.univ : Finset (U → I)))
    (t := (Finset.univ : Finset (Option V → J)))
    (f := fun (x : U → I) (y : Option V → J) =>
      w (x u) (y none) * F x (fun v => y (some v)))]
  rw [h]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (V → J)))
    (t := (Finset.univ : Finset (U → I)))
    (f := fun (x : V → J) (y : U → I) =>
      (∑ j : J, w (y u) j) * F y x)]

/-- Column-leaf elimination estimate: if `F` is nonnegative and every row sum of
`w` is at most `a`, then summing over the label of the new column leaf costs at
most the factor `a`. -/
theorem sum_column_leaf_mul_le_mul_sum (u : U) (a : ℝ) (w : I → J → ℝ)
    (F : (U → I) → (V → J) → ℝ)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ a)
    (hF : ∀ (x : U → I) (y : V → J), 0 ≤ F x y) :
    (∑ x : U → I, ∑ y : Option V → J,
        w (x u) (y none) * F x (fun v => y (some v))) ≤
      a * (∑ x : U → I, ∑ y : V → J, F x y) := by
  rw [sum_column_leaf_mul_eq_sum_row_sum_mul u w F]
  calc
    (∑ x : U → I, ∑ y : V → J, (∑ j : J, w (x u) j) * F x y)
        ≤ ∑ x : U → I, ∑ y : V → J, a * F x y := by
          refine Finset.sum_le_sum ?_
          intro x hx
          refine Finset.sum_le_sum ?_
          intro y hy
          exact mul_le_mul_of_nonneg_right (hrow (x u)) (hF x y)
    _ = ∑ x : U → I, a * (∑ y : V → J, F x y) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact (Finset.mul_sum (s := (Finset.univ : Finset (V → J)))
            (f := fun y : V → J => F x y) (a := a)).symm
    _ = a * (∑ x : U → I, ∑ y : V → J, F x y) := by
          exact (Finset.mul_sum (s := (Finset.univ : Finset (U → I)))
            (f := fun x : U → I => ∑ y : V → J, F x y) (a := a)).symm

/-- Off-tree factor cap: for a nonnegative weight array `w` whose entries are at
most `s`, the product of the `w`-weights over any finite set `A` of edges (with
arbitrary labelings `x`, `y`) is at most `s ^ A.card`. This is the factor
removed for each non-tree edge before leaf elimination. -/
theorem prod_bipartite_edge_weight_le_pow {U V I J E : Type*}
    {w : I → J → ℝ} {s : ℝ}
    (hwnn : ∀ i j, 0 ≤ w i j) (hw : ∀ i j, w i j ≤ s)
    (A : Finset E) (sr : E → U) (tg : E → V)
    (x : U → I) (y : V → J) :
    (Finset.prod A (fun e => w (x (sr e)) (y (tg e)))) ≤ s ^ A.card := by
  calc
    (Finset.prod A (fun e => w (x (sr e)) (y (tg e))))
        ≤ Finset.prod A (fun _ : E => s) := by
          exact Finset.prod_le_prod
            (fun e he => hwnn (x (sr e)) (y (tg e)))
            (fun e he => hw (x (sr e)) (y (tg e)))
    _ = s ^ A.card := Finset.prod_const s

/-- Split off-tree bound: if the edge set is the disjoint union `T ∪ O` (tree
edges `T` and off-tree edges `O`), the full product is at most the tree product
times `s ^ O.card`. The labelings `x`, `y` remain unrestricted functions. -/
theorem prod_bipartite_edge_weight_le_prod_mul_pow {U V I J E : Type*}
    [Fintype E] [DecidableEq E]
    {w : I → J → ℝ} {s : ℝ}
    (hwnn : ∀ i j, 0 ≤ w i j) (hw : ∀ i j, w i j ≤ s)
    (T O : Finset E) (hdisj : Disjoint T O) (huni : T ∪ O = univ)
    (sr : E → U) (tg : E → V)
    (x : U → I) (y : V → J) :
    (Finset.prod (univ : Finset E) (fun e => w (x (sr e)) (y (tg e)))) ≤
      (Finset.prod T (fun e => w (x (sr e)) (y (tg e)))) * s ^ O.card := by
  calc
    (Finset.prod (univ : Finset E) (fun e => w (x (sr e)) (y (tg e))))
        = Finset.prod (T ∪ O) (fun e => w (x (sr e)) (y (tg e))) := by
          rw [← huni]
    _ = (Finset.prod T (fun e => w (x (sr e)) (y (tg e)))) *
          (Finset.prod O (fun e => w (x (sr e)) (y (tg e)))) := by
          exact Finset.prod_union hdisj
    _ ≤ (Finset.prod T (fun e => w (x (sr e)) (y (tg e)))) * s ^ O.card := by
          exact mul_le_mul_of_nonneg_left
            (prod_bipartite_edge_weight_le_pow (A := O) hwnn hw sr tg x y)
            (Finset.prod_nonneg (fun e he => hwnn (x (sr e)) (y (tg e))))

end NLAlib

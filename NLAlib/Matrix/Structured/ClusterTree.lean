import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fintype.Sum

/-!
# Finite binary cluster trees

The index type of a node is the disjoint sum of its two child index types.
Consequently leaves partition the root, with no overlap or omitted indices.
Empty leaves and a tree consisting of a single leaf are allowed.
-/

namespace NLAlib

/-- A finite full binary cluster tree with a finite size at each leaf. -/
inductive ClusterTree where
  | leaf (size : ℕ)
  | node (left right : ClusterTree)
  deriving DecidableEq

namespace ClusterTree

/-- The root's coordinates, partitioned recursively by disjoint sums. -/
def Index : ClusterTree → Type
  | .leaf n => Fin n
  | .node l r => l.Index ⊕ r.Index

instance instFintypeIndex : (t : ClusterTree) → Fintype t.Index
  | .leaf _ => inferInstanceAs (Fintype (Fin _))
  | .node l r => letI := instFintypeIndex l; letI := instFintypeIndex r
                inferInstanceAs (Fintype (l.Index ⊕ r.Index))

instance instDecidableEqIndex : (t : ClusterTree) → DecidableEq t.Index
  | .leaf _ => inferInstanceAs (DecidableEq (Fin _))
  | .node l r => letI := instDecidableEqIndex l; letI := instDecidableEqIndex r
                inferInstanceAs (DecidableEq (l.Index ⊕ r.Index))

/-- Total root size. -/
def size : ClusterTree → ℕ
  | .leaf n => n
  | .node l r => l.size + r.size

/-- Maximum internal depth plus one; a leaf has height zero. -/
def height : ClusterTree → ℕ
  | .leaf _ => 0
  | .node l r => max l.height r.height + 1

/-- Number of leaves. -/
def leafCount : ClusterTree → ℕ
  | .leaf _ => 1
  | .node l r => l.leafCount + r.leafCount

/-- All leaves obey the requested leaf-size cap. -/
def LeafSizeLE (b : ℕ) : ClusterTree → Prop
  | .leaf n => n ≤ b
  | .node l r => l.LeafSizeLE b ∧ r.LeafSizeLE b

/-- Every leaf has at least the specified number of coordinates. -/
def LeafSizeGE (b : ℕ) : ClusterTree → Prop
  | .leaf n => b ≤ n
  | .node l r => l.LeafSizeGE b ∧ r.LeafSizeGE b

/-- A leaf-size lower bound controls the number of leaves. -/
theorem mul_leafCount_le_size (t : ClusterTree) (b : ℕ) (h : t.LeafSizeGE b) :
    b * t.leafCount ≤ t.size := by
  induction t with
  | leaf n => simpa only [leafCount, size, mul_one, LeafSizeGE] using h
  | node l r hl hr =>
    simpa only [leafCount, size, Nat.mul_add] using Nat.add_le_add (hl h.1) (hr h.2)

/-- A finite full binary tree always has a leaf, even when its index type is empty. -/
theorem leafCount_pos (t : ClusterTree) : 0 < t.leafCount := by
  induction t with
  | leaf n => exact Nat.zero_lt_one
  | node l r hl hr => exact Nat.add_pos_left hl _

@[simp] theorem card_index (t : ClusterTree) : Fintype.card t.Index = t.size := by
  induction t with
  | leaf n => exact Fintype.card_fin n
  | node l r hl hr =>
    change Fintype.card (l.Index ⊕ r.Index) = l.size + r.size
    rw [Fintype.card_sum, hl, hr]

end ClusterTree
end NLAlib

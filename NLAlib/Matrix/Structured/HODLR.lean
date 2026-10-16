import NLAlib.Matrix.Structured.ClusterTree
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# HODLR storage and factorized matrix-vector multiplication

Each node stores the two directed sibling blocks by separate low-rank factors.
The recursive reconstruction and matvec use the actual stored factors. Scalar
costs count one multiplication and one accumulated addition per dense entry;
indexing, gathering, and conjugation have zero cost.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Stored HODLR data on a full binary cluster tree. -/
inductive HODLR (K : Type*) [RCLike K] : ClusterTree → Type _ where
  | leaf {n : ℕ} (D : Matrix (Fin n) (Fin n) K) : HODLR K (.leaf n)
  | node {l r : ClusterTree} (left : HODLR K l) (right : HODLR K r)
      (p q : ℕ) (U : Matrix l.Index (Fin p) K) (V : Matrix r.Index (Fin p) K)
      (W : Matrix r.Index (Fin q) K) (Z : Matrix l.Index (Fin q) K) :
      HODLR K (.node l r)

namespace HODLR
variable {K : Type*} [RCLike K]

/-- The unique matrix reconstructed from the stored leaf and sibling blocks. -/
def matrix : {t : ClusterTree} → HODLR K t → Matrix t.Index t.Index K
  | _, .leaf D => D
  | _, .node dl dr _ _ U V W Z =>
      Matrix.fromBlocks dl.matrix (U * Vᴴ) (W * Zᴴ) dr.matrix

/-- Number of stored scalar entries. -/
def storage : {t : ClusterTree} → HODLR K t → ℕ
  | .leaf n, .leaf _ => n * n
  | .node l r, .node dl dr p q _ _ _ _ =>
      dl.storage + dr.storage + (p + q) * (l.size + r.size)

/-- Every stored directed sibling factor has at most `k` columns. -/
def RanksLE (k : ℕ) : {t : ClusterTree} → HODLR K t → Prop
  | _, .leaf _ => True
  | _, .node dl dr p q _ _ _ _ => p ≤ k ∧ q ≤ k ∧ dl.RanksLE k ∧ dr.RanksLE k

/-- Evaluate a dense matrix-vector product, accumulating into an existing
vector. The finite sum is the usual loop with one multiply and one add per entry. -/
def denseAccumulate {m n : Type*} [Fintype n] (A : Matrix m n K)
    (x : n → K) (y : m → K) : m → K := fun i => y i + ∑ j, A i j * x j

theorem denseAccumulate_eq {m n : Type*} [Fintype n] (A : Matrix m n K)
    (x : n → K) (y : m → K) : denseAccumulate A x y = y + A *ᵥ x := rfl

/-- Recursive matvec: compute the diagonal child products, project each input
through the opposite column basis, and accumulate through the row basis. -/
def apply : {t : ClusterTree} → HODLR K t → (t.Index → K) → (t.Index → K)
  | _, .leaf D, x => denseAccumulate D x 0
  | _, .node dl dr _ _ U V W Z, x =>
      Sum.elim
        (denseAccumulate U (denseAccumulate Vᴴ (x ∘ Sum.inr) 0)
          (dl.apply (x ∘ Sum.inl)))
        (denseAccumulate W (denseAccumulate Zᴴ (x ∘ Sum.inl) 0)
          (dr.apply (x ∘ Sum.inr)))

/-- Scalar multiplication/addition actions performed by the accumulation loops.
This counts the actual four factor applications at each internal node. -/
def actions : {t : ClusterTree} → HODLR K t → ℕ
  | .leaf n, .leaf _ => 2 * n * n
  | .node l r, .node dl dr p q _ _ _ _ =>
      dl.actions + dr.actions +
        2 * p * r.size + 2 * l.size * p + 2 * q * l.size + 2 * r.size * q

/-- The stored-factor matvec returns the reconstructed matrix-vector product.
Source: user derivations, HODLR storage and matvec.
atlas: hodlr-storage-matvec (partial) -/
theorem apply_eq_mulVec {t : ClusterTree} (H : HODLR K t) (x : t.Index → K) :
    H.apply x = H.matrix *ᵥ x := by
  induction H with
  | leaf D =>
      funext i
      change 0 + ∑ j, D i j * x j = ∑ j, D i j * x j
      simp
  | node dl dr p q U V W Z hl hr =>
      change Sum.elim _ _ = (Matrix.fromBlocks dl.matrix (U * Vᴴ) (W * Zᴴ) dr.matrix) *ᵥ x
      rw [Matrix.fromBlocks_mulVec]
      rw [hl, hr]
      simp only [denseAccumulate_eq, zero_add, ← Matrix.mulVec_mulVec]
      rw [add_comm (dr.matrix *ᵥ (x ∘ Sum.inr))]

/-- The explicit scalar-action count is twice the stored scalar count. -/
theorem actions_eq_two_mul_storage {t : ClusterTree} (H : HODLR K t) :
    H.actions = 2 * H.storage := by
  induction H with
  | leaf D => simp only [actions, storage]; ring
  | node dl dr p q U V W Z hl hr => simp only [actions, storage, hl, hr]; ring

/-- The storage bound includes zero ranks, empty clusters, and a root leaf.
`height ≤ L` is exactly the condition that internal depths are below `L`.
Source: user derivations, HODLR storage bound.
atlas: hodlr-storage-matvec -/
theorem storage_le {t : ClusterTree} (H : HODLR K t) (b k L : ℕ)
    (hb : t.LeafSizeLE b) (hk : H.RanksLE k) (hL : t.height ≤ L) :
    H.storage ≤ t.size * b + 2 * t.size * k * L := by
  suffices h : H.storage ≤ t.size * b + 2 * t.size * k * t.height by
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hL) _)
  clear hL L
  induction H with
  | leaf D => simpa [storage, ClusterTree.size, ClusterTree.height] using Nat.mul_le_mul_left _ hb
  | @node l r dl dr p q U V W Z hl hr =>
      rcases hk with ⟨hp, hq, hdl, hdr⟩
      have hleft := hl hb.1 hdl
      have hright := hr hb.2 hdr
      have hlh : l.height ≤ max l.height r.height := le_max_left _ _
      have hrh : r.height ≤ max l.height r.height := le_max_right _ _
      have hleft' : dl.storage ≤ l.size * b + 2 * l.size * k * max l.height r.height :=
        hleft.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlh) _)
      have hright' : dr.storage ≤ r.size * b + 2 * r.size * k * max l.height r.height :=
        hright.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hrh) _)
      have hpq : (p + q) * (l.size + r.size) ≤ (2 * k) * (l.size + r.size) := by
        exact Nat.mul_le_mul_right _ (by omega)
      simp only [storage, ClusterTree.size, ClusterTree.height]
      nlinarith

end HODLR
end NLAlib

import NLAlib.Matrix.Structured.HODLR

/-!
# Nested HSS bases and the two-pass matvec

Nested row and column bases are data, with their transfer relations realized
by construction. The upward and downward passes apply those stored transfers
and sibling couplings; their output is the actual reconstructed matrix product.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- An HSS representation with a common padded row/column rank at each node.
Padding permits row and column spaces of different original dimensions. -/
inductive HSS (K : Type*) [RCLike K] : ClusterTree → ℕ → Type _ where
  | leaf {n r : ℕ} (D : Matrix (Fin n) (Fin n) K)
      (U V : Matrix (Fin n) (Fin r) K) : HSS K (.leaf n) r
  | node {l r : ClusterTree} {p q s : ℕ} (left : HSS K l p) (right : HSS K r q)
      (E F : Matrix (Fin p ⊕ Fin q) (Fin s) K)
      (B : Matrix (Fin p) (Fin q) K) (C : Matrix (Fin q) (Fin p) K) :
      HSS K (.node l r) s

namespace HSS
variable {K : Type*} [RCLike K]

/-- The nested row basis. -/
def rowBasis : {t : ClusterTree} → {r : ℕ} → HSS K t r → Matrix t.Index (Fin r) K
  | _, _, .leaf _ U _ => U
  | _, _, .node dl dr E _ _ _ => Matrix.fromBlocks dl.rowBasis 0 0 dr.rowBasis * E

/-- The nested column basis. -/
def colBasis : {t : ClusterTree} → {r : ℕ} → HSS K t r → Matrix t.Index (Fin r) K
  | _, _, .leaf _ _ V => V
  | _, _, .node dl dr _ F _ _ => Matrix.fromBlocks dl.colBasis 0 0 dr.colBasis * F

/-- The matrix represented by leaf diagonal blocks and nested sibling couplings. -/
def matrix : {t : ClusterTree} → {r : ℕ} → HSS K t r → Matrix t.Index t.Index K
  | _, _, .leaf D _ _ => D
  | _, _, .node dl dr _ _ B C => Matrix.fromBlocks dl.matrix
      (dl.rowBasis * B * dr.colBasisᴴ) (dr.rowBasis * C * dl.colBasisᴴ) dr.matrix

/-- The upward pass computes the column-basis coordinates. -/
def upward : {t : ClusterTree} → {r : ℕ} → HSS K t r → (t.Index → K) → (Fin r → K)
  | _, _, .leaf _ _ V, x => HODLR.denseAccumulate Vᴴ x 0
  | _, _, .node dl dr _ F _ _, x =>
      HODLR.denseAccumulate Fᴴ
        (Sum.elim (dl.upward (x ∘ Sum.inl)) (dr.upward (x ∘ Sum.inr))) 0

/-- The downward pass propagates a row-basis contribution and accumulates
sibling interactions before reaching each dense leaf. -/
def downward : {t : ClusterTree} → {r : ℕ} → HSS K t r →
    (t.Index → K) → (Fin r → K) → (t.Index → K)
  | _, _, .leaf D U _, x, z => HODLR.denseAccumulate U z (HODLR.denseAccumulate D x 0)
  | _, _, .node dl dr E _ B C, x, z =>
      let ez := HODLR.denseAccumulate E z 0
      Sum.elim
        (dl.downward (x ∘ Sum.inl)
          (HODLR.denseAccumulate B (dr.upward (x ∘ Sum.inr)) (ez ∘ Sum.inl)))
        (dr.downward (x ∘ Sum.inr)
          (HODLR.denseAccumulate C (dl.upward (x ∘ Sum.inl)) (ez ∘ Sum.inr)))

/-- The upward pass stores the projection at every node for reuse by the
downward pass, so projections are computed once. -/
def Cache : {t : ClusterTree} → {r : ℕ} → HSS K t r → Type _
  | _, r, .leaf _ _ _ => Fin r → K
  | _, s, .node dl dr _ _ _ _ => (Fin s → K) × dl.Cache × dr.Cache

/-- The projection stored at the root of a cached subtree. -/
def cacheValue : {t : ClusterTree} → {r : ℕ} → (H : HSS K t r) → H.Cache → (Fin r → K)
  | _, _, .leaf _ _ _, c => c
  | _, _, .node _ _ _ _ _ _, c => c.1

/-- Build all upward projections with one traversal of the stored HSS data. -/
def upwardPass : {t : ClusterTree} → {r : ℕ} → (H : HSS K t r) →
    (t.Index → K) → H.Cache
  | _, _, .leaf _ _ V, x => HODLR.denseAccumulate Vᴴ x 0
  | _, _, .node dl dr _ F _ _, x =>
      let cl := dl.upwardPass (x ∘ Sum.inl)
      let cr := dr.upwardPass (x ∘ Sum.inr)
      (HODLR.denseAccumulate Fᴴ (Sum.elim (dl.cacheValue cl) (dr.cacheValue cr)) 0, cl, cr)

/-- The downward traversal reads each sibling's cached projection. -/
def downwardPass : {t : ClusterTree} → {r : ℕ} → (H : HSS K t r) → H.Cache →
    (t.Index → K) → (Fin r → K) → (t.Index → K)
  | _, _, .leaf D U _, _, x, z => HODLR.denseAccumulate U z (HODLR.denseAccumulate D x 0)
  | _, _, .node dl dr E _ B C, c, x, z =>
      let ez := HODLR.denseAccumulate E z 0
      Sum.elim
        (dl.downwardPass c.2.1 (x ∘ Sum.inl)
          (HODLR.denseAccumulate B (dr.cacheValue c.2.2) (ez ∘ Sum.inl)))
        (dr.downwardPass c.2.2 (x ∘ Sum.inr)
          (HODLR.denseAccumulate C (dl.cacheValue c.2.1) (ez ∘ Sum.inr)))

/-- The stored root projection agrees with the mathematical upward recursion. -/
theorem cacheValue_upwardPass {t : ClusterTree} {r : ℕ} (H : HSS K t r) (x : t.Index → K) :
    H.cacheValue (H.upwardPass x) = H.upward x := by
  induction H with
  | leaf D U V => rfl
  | node dl dr E F B C hl hr =>
    change HODLR.denseAccumulate Fᴴ
      (Sum.elim (dl.cacheValue (dl.upwardPass (x ∘ Sum.inl)))
        (dr.cacheValue (dr.upwardPass (x ∘ Sum.inr)))) 0 =
      HODLR.denseAccumulate Fᴴ
        (Sum.elim (dl.upward (x ∘ Sum.inl)) (dr.upward (x ∘ Sum.inr))) 0
    rw [hl, hr]

/-- Cached execution realizes the downward recursion. -/
theorem downwardPass_upwardPass {t : ClusterTree} {r : ℕ} (H : HSS K t r)
    (x : t.Index → K) (z : Fin r → K) :
    H.downwardPass (H.upwardPass x) x z = H.downward x z := by
  induction H with
  | leaf D U V => rfl
  | node dl dr E F B C hl hr =>
    simp [downwardPass, upwardPass, cacheValue_upwardPass, downward, hl, hr]

/-- The number of stored scalar entries in this HSS representation. -/
def storage : {t : ClusterTree} → {r : ℕ} → HSS K t r → ℕ
  | .leaf n, r, .leaf _ _ _ => n * n + 2 * n * r
  | _, s, @HSS.node _ _ _ _ p q _ dl dr _ _ _ _ =>
      dl.storage + dr.storage + 2 * (p + q) * s + 2 * p * q

/-- Scalar actions in one complete upward/downward matvec, counting one
multiply and accumulated add per stored dense coefficient. -/
def actions : {t : ClusterTree} → {r : ℕ} → HSS K t r → ℕ
  | .leaf n, r, .leaf _ _ _ => 2 * n * n + 4 * n * r
  | _, s, @HSS.node _ _ _ _ p q _ dl dr _ _ _ _ =>
      dl.actions + dr.actions + 4 * (p + q) * s + 4 * p * q

/-- All nested basis ranks are bounded, including the current root rank. -/
def RanksLE (k : ℕ) : {t : ClusterTree} → {r : ℕ} → HSS K t r → Prop
  | _, r, .leaf _ _ _ => r ≤ k
  | _, s, .node dl dr _ _ _ _ => s ≤ k ∧ dl.RanksLE k ∧ dr.RanksLE k

/-- The rank bound applies in particular to the current node. -/
theorem rank_le_of_ranksLE {t : ClusterTree} {r k : ℕ} (H : HSS K t r)
    (h : H.RanksLE k) : r ≤ k := by cases H with
  | leaf D U V => exact h
  | node dl dr E F B C => exact h.1

/-- The upward pass exactly equals projection onto the reconstructed nested
column basis. -/
theorem upward_eq {t : ClusterTree} {r : ℕ} (H : HSS K t r) (x : t.Index → K) :
    H.upward x = H.colBasisᴴ *ᵥ x := by
  induction H with
  | leaf D U V => simp [upward, colBasis, HODLR.denseAccumulate_eq]
  | node dl dr E F B C hl hr =>
      change HODLR.denseAccumulate Fᴴ
        (Sum.elim (dl.upward (x ∘ Sum.inl)) (dr.upward (x ∘ Sum.inr))) 0 =
          (Matrix.fromBlocks dl.colBasis 0 0 dr.colBasis * F)ᴴ *ᵥ x
      rw [HODLR.denseAccumulate_eq, zero_add, hl, hr, Matrix.conjTranspose_mul,
        Matrix.fromBlocks_conjTranspose, ← Matrix.mulVec_mulVec]
      simp only [Matrix.conjTranspose_zero, Matrix.fromBlocks_mulVec,
        Matrix.zero_mulVec, add_zero, zero_add]

/-- The downward pass returns `A x + U z`, including all nested transfers and
sibling interactions. Source: user derivations, HSS two-pass matvec.
atlas: hss-nested-bases-matvec (partial) -/
theorem downward_eq {t : ClusterTree} {r : ℕ} (H : HSS K t r)
    (x : t.Index → K) (z : Fin r → K) :
    H.downward x z = H.matrix *ᵥ x + H.rowBasis *ᵥ z := by
  induction H with
  | leaf D U V => simp [downward, matrix, rowBasis, HODLR.denseAccumulate_eq]
  | node dl dr E F B C hl hr =>
      change (HSS.node dl dr E F B C).downward x z =
        Matrix.fromBlocks dl.matrix (dl.rowBasis * B * dr.colBasisᴴ)
          (dr.rowBasis * C * dl.colBasisᴴ) dr.matrix *ᵥ x +
        (Matrix.fromBlocks dl.rowBasis 0 0 dr.rowBasis * E) *ᵥ z
      simp only [downward, HODLR.denseAccumulate_eq, zero_add, hl, hr, upward_eq]
      rw [← Matrix.mulVec_mulVec z, Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
      funext i
      cases i <;> simp [Pi.add_apply, Function.comp_def, Matrix.mulVec_add,
        ← Matrix.mulVec_mulVec,
        add_left_comm, add_comm]

/-- A zero-rank root eliminates the external contribution and the two-pass
algorithm returns the actual matrix-vector product. -/
theorem downward_zero_eq_mulVec {t : ClusterTree} (H : HSS K t 0) (x : t.Index → K) :
    H.downward x 0 = H.matrix *ᵥ x := by rw [downward_eq]; simp

/-- The actual cached two-pass algorithm returns the represented matrix product. -/
theorem downwardPass_upwardPass_zero_eq_mulVec {t : ClusterTree} (H : HSS K t 0)
    (x : t.Index → K) : H.downwardPass (H.upwardPass x) x 0 = H.matrix *ᵥ x := by
  rw [downwardPass_upwardPass, downward_zero_eq_mulVec]

/-- The scalar-action count of the two passes is twice the stored entry count. -/
theorem actions_eq_two_mul_storage {t : ClusterTree} {r : ℕ} (H : HSS K t r) :
    H.actions = 2 * H.storage := by
  induction H with
  | leaf D U V => simp only [actions, storage]; ring
  | node dl dr E F B C hl hr => simp only [actions, storage, hl, hr]; ring

/-- General HSS storage bound in terms of leaf count and size.
Source: user derivations, HSS storage formula.
atlas: hss-nested-bases-matvec (partial) -/
theorem storage_le {t : ClusterTree} {r : ℕ} (H : HSS K t r) (b k : ℕ)
    (hb : t.LeafSizeLE b) (hk : H.RanksLE k) :
    H.storage ≤ t.size * b + 2 * t.size * k + 6 * k ^ 2 * (t.leafCount - 1) := by
  induction H with
  | leaf D U V =>
      simp only [storage, ClusterTree.size, ClusterTree.leafCount, Nat.sub_self,
        mul_zero, add_zero]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hk)
  | @node l r p q s dl dr E F B C hl hr =>
      rcases hk with ⟨hs, hdl, hdr⟩
      have hp : p ≤ k := dl.rank_le_of_ranksLE hdl
      have hq : q ≤ k := dr.rank_le_of_ranksLE hdr
      have hlc : 1 ≤ l.leafCount := l.leafCount_pos
      have hrc : 1 ≤ r.leafCount := r.leafCount_pos
      have hcost : 2 * (p + q) * s + 2 * p * q ≤ 6 * k ^ 2 := by
        calc
          _ ≤ 2 * (k + k) * k + 2 * k * k := by gcongr
          _ = _ := by ring
      have hleft := hl hb.1 hdl
      have hright := hr hb.2 hdr
      simp only [storage, ClusterTree.size, ClusterTree.leafCount]
      have hc : l.leafCount + r.leafCount - 1 = (l.leafCount - 1) + (r.leafCount - 1) + 1 := by omega
      rw [hc]
      nlinarith

/-- With leaf sizes between `k` and `2k`, the actual nested representation
uses at most `10 N k` scalars, and its cached two-pass matvec uses twice its
storage in scalar multiplication/addition actions.
Source: user derivations, HSS matvec and storage.
atlas: hss-nested-bases-matvec -/
theorem storage_le_ten_mul_size_mul_rank {t : ClusterTree} (H : HSS K t 0) (k : ℕ)
    (_hkpos : 1 ≤ k) (hlower : t.LeafSizeGE k) (hupper : t.LeafSizeLE (2 * k))
    (hk : H.RanksLE k) : H.storage ≤ 10 * t.size * k := by
  have h := H.storage_le (2 * k) k hupper hk
  have hleaves := t.mul_leafCount_le_size k hlower
  have hsub : t.leafCount - 1 ≤ t.leafCount := Nat.sub_le _ _
  have hbudget : 6 * k ^ 2 * (t.leafCount - 1) ≤ 6 * t.size * k := by
    calc
      _ ≤ 6 * k ^ 2 * t.leafCount := Nat.mul_le_mul_left _ hsub
      _ = (6 * k) * (k * t.leafCount) := by ring
      _ ≤ (6 * k) * t.size := Nat.mul_le_mul_left _ hleaves
      _ = _ := by ring
  nlinarith

end HSS
end NLAlib

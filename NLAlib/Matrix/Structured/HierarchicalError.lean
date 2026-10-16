import NLAlib.Matrix.Structured.HODLR
import NLAlib.Matrix.Norms.BlockDiagonalBounds

/-!
# Levelwise hierarchical matrix error

An arbitrary matrix on a binary cluster tree is represented by its dense leaf
blocks and its two directed sibling blocks. The error bounds concern these
actual blocks, independently of how low-rank approximations were obtained.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A block tree with arbitrary sibling blocks, in particular compression errors. -/
inductive ClusterMatrix (K : Type*) [RCLike K] : ClusterTree → Type _ where
  | leaf {n : ℕ} (D : Matrix (Fin n) (Fin n) K) : ClusterMatrix K (.leaf n)
  | node {l r : ClusterTree} (left : ClusterMatrix K l) (right : ClusterMatrix K r)
      (B : Matrix l.Index r.Index K) (C : Matrix r.Index l.Index K) :
      ClusterMatrix K (.node l r)

namespace ClusterMatrix
variable {K : Type*} [RCLike K]

/-- Reconstruct the error matrix from the disjoint block partition. -/
def matrix : {t : ClusterTree} → ClusterMatrix K t → Matrix t.Index t.Index K
  | _, .leaf D => D
  | _, .node dl dr B C => Matrix.fromBlocks dl.matrix B C dr.matrix

/-- Sum of squared Frobenius errors over all leaves and directed sibling blocks. -/
def blockFrobSq : {t : ClusterTree} → ClusterMatrix K t → ℝ
  | _, .leaf D => frobSq D
  | _, .node dl dr B C => dl.blockFrobSq + dr.blockFrobSq + frobSq B + frobSq C

/-- Leaves have error at most `εD`, and sibling blocks at depth `depth` have
error at most `ε depth`. -/
def ErrorsLE (εD : ℝ) (ε : ℕ → ℝ) :
    {t : ClusterTree} → ClusterMatrix K t → ℕ → Prop
  | _, .leaf D, _ => specNorm D ≤ εD
  | _, .node dl dr B C, depth =>
      specNorm B ≤ ε depth ∧ specNorm C ≤ ε depth ∧
        dl.ErrorsLE εD ε (depth + 1) ∧ dr.ErrorsLE εD ε (depth + 1)

/-- Exact Frobenius Pythagoras over the complete hierarchical partition.
Source: user derivations, HODLR levelwise error.
atlas: hodlr-levelwise-compression-error (partial) -/
theorem frobSq_matrix_eq {t : ClusterTree} (E : ClusterMatrix K t) :
    frobSq E.matrix = E.blockFrobSq := by
  induction E with
  | leaf D => rfl
  | node dl dr B C hl hr =>
    change frobSq (Matrix.fromBlocks dl.matrix B C dr.matrix) = _
    rw [frobSq_fromBlocks, hl, hr]
    change _ = dl.blockFrobSq + dr.blockFrobSq + frobSq B + frobSq C
    ring

/-- The depthwise spectral errors add once per level, with no factor from
the number of sibling blocks at that level. Includes unbalanced trees and
root leaves. Source: user derivations, HODLR levelwise compression error.
atlas: hodlr-levelwise-compression-error -/
theorem specNorm_matrix_le {t : ClusterTree} (E : ClusterMatrix K t)
    (εD : ℝ) (ε : ℕ → ℝ) (_hD : 0 ≤ εD) (hε : ∀ j, 0 ≤ ε j)
    (depth L : ℕ) (hL : t.height ≤ L) (hE : E.ErrorsLE εD ε depth) :
    specNorm E.matrix ≤ εD + ∑ j ∈ Finset.range L, ε (depth + j) := by
  induction L generalizing t depth with
  | zero =>
    cases E with
    | leaf D => simpa [matrix, ErrorsLE] using hE
    | node dl dr B C => simp [ClusterTree.height] at hL
  | succ L hrec =>
    cases E with
    | leaf D =>
      exact hE.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hε _))
    | @node l r dl dr B C =>
      rcases hE with ⟨hB, hC, hdl, hdr⟩
      have hlL : l.height ≤ L := by simp only [ClusterTree.height] at hL; omega
      have hrL : r.height ≤ L := by simp only [ClusterTree.height] at hL; omega
      have hl := hrec dl (depth + 1) hlL hdl
      have hr := hrec dr (depth + 1) hrL hdr
      have hsplit : Matrix.fromBlocks dl.matrix B C dr.matrix = Matrix.fromBlocks dl.matrix 0 0 dr.matrix +
          Matrix.fromBlocks 0 B C 0 := by ext i j; cases i <;> cases j <;> simp
      change specNorm (Matrix.fromBlocks dl.matrix B C dr.matrix) ≤ _
      rw [hsplit]
      calc
        _ ≤ specNorm (Matrix.fromBlocks dl.matrix 0 0 dr.matrix) +
            specNorm (Matrix.fromBlocks 0 B C 0) := specNorm_add_le _ _
        _ ≤ max (specNorm dl.matrix) (specNorm dr.matrix) + max (specNorm B) (specNorm C) :=
          add_le_add (specNorm_fromBlocks_diagonal_le _ _) (specNorm_fromBlocks_offDiagonal_le _ _)
        _ ≤ (εD + ∑ j ∈ Finset.range L, ε (depth + 1 + j)) + ε depth :=
          add_le_add (max_le hl hr) (max_le hB hC)
        _ = _ := by
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm 1 depth]
          ring

end ClusterMatrix

/-- The difference between two HODLR representations on the same tree,
resolved into precisely the leaf and sibling compression errors. -/
def HODLR.error {K : Type*} [RCLike K] : {t : ClusterTree} →
    HODLR K t → HODLR K t → ClusterMatrix K t
  | _, .leaf D, .leaf D' => .leaf (D - D')
  | _, .node dl dr _ _ U V W Z, .node dl' dr' _ _ U' V' W' Z' =>
      .node (dl.error dl') (dr.error dr') (U * Vᴴ - U' * V'ᴴ) (W * Zᴴ - W' * Z'ᴴ)

/-- Reconstruction of the blockwise errors equals the actual matrix difference. -/
theorem HODLR.matrix_error {K : Type*} [RCLike K] {t : ClusterTree}
    (H H' : HODLR K t) : (H.error H').matrix = H.matrix - H'.matrix := by
  induction H with
  | leaf D => cases H'; rfl
  | node dl dr p q U V W Z hl hr =>
    cases H' with
    | node dl' dr' p' q' U' V' W' Z' =>
      simp only [HODLR.error, ClusterMatrix.matrix, HODLR.matrix, hl, hr]
      ext i j; cases i <;> cases j <;> rfl

end NLAlib

import NLAlib.Matrix.InterlacingOrthogonalTransport

/-!
# Relabeling diagonal interlacing constructions

Finite root lists and arbitrary finite matrix labels are connected by actual
matrix reindexing; characteristic polynomials are unchanged. These helpers
retain empty shapes and do not require a chosen ordering on matrix labels.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Relabeling every leading coordinate of a diagonal arrowhead leaves its
characteristic polynomial unchanged. Source: permutation similarity;
helper for the arbitrary-finite-shape converse-interlacing constructions. -/
theorem charpoly_diagonal_arrowhead_reindex (e : n ≃ m) (d v : n → ℝ) (a : ℝ) :
    (Matrix.fromBlocks (Matrix.diagonal (d ∘ e.symm)) (Matrix.replicateCol (Fin 1) (v ∘ e.symm))
      (Matrix.replicateRow (Fin 1) (v ∘ e.symm)) (Matrix.of fun _ _ : Fin 1 => a)).charpoly =
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
      (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a)).charpoly := by
  rw [← Matrix.charpoly_reindex (e.sumCongr (Equiv.refl (Fin 1)))
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
      (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a))]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix, Matrix.fromBlocks, Matrix.diagonal_apply,
      Function.comp_def]

/-- Relabeling a diagonal rank-one update leaves its characteristic
polynomial unchanged. Source: permutation similarity; helper for converse
interlacing on arbitrary finite matrix labels. -/
theorem charpoly_diagonal_add_vecMulVec_reindex (e : n ≃ m) (d v : n → ℝ) :
    (Matrix.diagonal (d ∘ e.symm) + Matrix.vecMulVec (v ∘ e.symm) (v ∘ e.symm)).charpoly =
      (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly := by
  rw [← Matrix.charpoly_reindex e (Matrix.diagonal d + Matrix.vecMulVec v v)]
  congr 1
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix, Matrix.diagonal_apply, Matrix.vecMulVec,
    Function.comp_def]

end NLAlib

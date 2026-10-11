import NLAlib.Sketching.SparseFock.SparseEmbedding
import NLAlib.Sketching.Gram

/-!
# The SparseStack proof uses the library's embedding predicate

The Euclidean-vector predicate used by the pinned sparse-Fock proof is
identified with `IsSubspaceEmbedding`. This bridge includes empty index types.
Source: operator manuscript `sh:sparse`; pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- On an orthonormal frame, the library embedding predicate is exactly the
two-sided Euclidean squared-norm inequality used in the sparse proof.
Source: manuscript `sh:sparse`, coordinate identification; supports `sparse-ose`. -/
theorem isSubspaceEmbedding_iff_applyRectMatrix_bounds
    {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (S : Matrix ρ ι ℝ) {U : Matrix ι κ ℝ} (hU : HasOrthonormalCols U) (ε : ℝ) :
    IsSubspaceEmbedding S U ε ↔ ∀ x : EuclideanSpace ℝ κ,
      (1 - ε) * ‖x‖ ^ 2 ≤
        ‖SparseFock.MatrixTail.applyRectMatrix (S * U) x‖ ^ 2 ∧
      ‖SparseFock.MatrixTail.applyRectMatrix (S * U) x‖ ^ 2 ≤
        (1 + ε) * ‖x‖ ^ 2 := by
  rw [isSubspaceEmbedding_iff_of_hasOrthonormalCols hU]
  constructor
  · intro h x
    simpa only [SparseFock.MatrixTail.applyRectMatrix, EuclideanSpace.real_norm_sq_eq,
      WithLp.ofLp_toLp, dotProduct, ← pow_two] using h (WithLp.ofLp x)
  · intro h x
    simpa only [SparseFock.MatrixTail.applyRectMatrix, EuclideanSpace.real_norm_sq_eq,
      WithLp.ofLp_toLp, dotProduct, ← pow_two] using h (WithLp.toLp 2 x)

/-- The SparseStack source predicate is the library's subspace embedding
predicate, for any outcome and any distortion.
Source: pinned sparse-Fock matrix endpoint; supports `sparse-ose`. -/
theorem isMatrixSparseStackOSE_iff_isSubspaceEmbedding
    {s b n d : ℕ} {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U)
    (Z : SparseFock.SparseStackModel.Sample s b n) (ε : ℝ) :
    SparseFock.MainTheorem.IsMatrixSparseStackOSE U Z ε ↔
      IsSubspaceEmbedding (SparseFock.SparseStackModel.stackMatrix Z) U ε :=
  (isSubspaceEmbedding_iff_applyRectMatrix_bounds _ hU ε).symm

end NLAlib

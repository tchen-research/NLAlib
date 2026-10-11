import NLAlib.Sketching.SparseEmbeddingTransport
import NLAlib.Sketching.FiniteIndexTransport

/-!
# Sparse embedding laws on arbitrary finite coordinate types

The public frames use arbitrary finite ambient and coefficient indices.
Enumeration is internal to the literal finite Fock construction; users do not
need to reindex their matrices. Actual laws, constants and column sparsity
are unchanged by this coordinate transport. Source: manuscript `sh:sparse`
and `sh:exact-s`; pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib
open SparseFock.PaperParameters SparseFock.MainTheoremAssembly

/-- A literal SparseStack sketch with arbitrary finite input-column labels.
Source: the pinned signed-selector construction; supports `sparse-ose`. -/
def sparseStackMatrixOn (ι : Type*) [Fintype ι] {s b : ℕ}
    (z : SparseFock.SparseStackDistribution.RawSample s b (Fintype.card ι)) :
    Matrix (Fin s × Fin b) ι ℝ :=
  (SparseFock.SparseStackModel.stackMatrix
    (SparseFock.SparseStackDistribution.toSample z)).reindex
      (Equiv.refl _) (Fintype.equivFin ι).symm

/-- A uniform signed exact-s sketch with arbitrary finite input-column labels.
Source: the pinned uniform-support construction; supports `sparse-ose`. -/
def uniformSparseMatrixOn (ι : Type*) [Fintype ι] {m s : ℕ}
    (X : SparseFock.UniformExactS.ExactSample m s (Fintype.card ι)) :
    Matrix (Fin m) ι ℝ :=
  (SparseFock.UniformExactS.sketchMatrix X).reindex
    (Equiv.refl _) (Fintype.equivFin ι).symm

/-- Relabelling a concrete sketch back to the user's finite ambient indices
preserves the embedding event for the internally enumerated frame.
Source: the library Gram equivalence and orthonormal reindexing;
supports `sparse-ose`. -/
theorem isSubspaceEmbedding_reindex_equivFin_symm_iff
    {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    {U : Matrix ι κ ℝ} (hU : HasOrthonormalCols U)
    (S : Matrix ρ (Fin (Fintype.card ι)) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsSubspaceEmbedding (S.reindex (Equiv.refl _) (Fintype.equivFin ι).symm) U ε ↔
      IsSubspaceEmbedding S
        (U.reindex (Fintype.equivFin ι) (Fintype.equivFin κ)) ε := by
  have h := isSubspaceEmbedding_reindex_iff (S := S)
    (hU.reindex (Fintype.equivFin ι) (Fintype.equivFin κ))
    (Equiv.refl ρ) (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm hε
  have hUback :
      (U.reindex (Fintype.equivFin ι) (Fintype.equivFin κ)).reindex
        (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm = U := by
    ext i j
    simp [Matrix.reindex_apply]
  rwa [hUback] at h

/-- Actual SparseStack sampling embeds any fixed finite-index orthonormal
frame with probability at least 1-delta, using the same explicit rounded
parameters as its literal matrix theorem; includes empty coefficient indices.
Source: manuscript `sh:sparse`, finite-coordinate transport.
atlas: sparse-ose -/
theorem measure_sparseStack_embedding_success_ge_fintype
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix ι κ ℝ} (hU : HasOrthonormalCols U) :
    1 - δ ≤
      (sparseStackMeasure (roundedS (failureOrder (Fintype.card κ) δ) ε)
        (roundedB (Fintype.card κ) (failureOrder (Fintype.card κ) δ) ε)
        (Fintype.card ι) (canonicalB_pos hε hε1)).real
      {z | IsSubspaceEmbedding (sparseStackMatrixOn ι z) U ε} := by
  have hevent : {z : SparseFock.SparseStackDistribution.RawSample
        (roundedS (failureOrder (Fintype.card κ) δ) ε)
        (roundedB (Fintype.card κ) (failureOrder (Fintype.card κ) δ) ε)
        (Fintype.card ι) | IsSubspaceEmbedding (sparseStackMatrixOn ι z) U ε} =
      {z | IsSubspaceEmbedding (SparseFock.SparseStackModel.stackMatrix
        (SparseFock.SparseStackDistribution.toSample z))
        (U.reindex (Fintype.equivFin ι) (Fintype.equivFin κ)) ε} := by
    ext z
    exact isSubspaceEmbedding_reindex_equivFin_symm_iff hU _ hε.le
  rw [hevent]
  exact measure_sparseStack_embedding_success_ge hδ hδ1 hε hε1
    (hU.reindex (Fintype.equivFin ι) (Fintype.equivFin κ))

/-- Independent uniform signed exact-s columns embed any fixed finite-index
orthonormal frame with probability at least 1-delta, including empty frames.
Source: manuscript `sh:exact-s`, finite-coordinate transport.
atlas: sparse-ose -/
theorem measure_uniformSparse_embedding_success_ge_fintype
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix ι κ ℝ} (hU : HasOrthonormalCols U) :
    1 - δ ≤
      (uniformSparseMeasure
        (roundedS (failureOrder (Fintype.card κ) δ) ε *
          roundedB (Fintype.card κ) (failureOrder (Fintype.card κ) δ) ε)
        (roundedS (failureOrder (Fintype.card κ) δ) ε) (Fintype.card ι)
        (SparseFock.UniformExactS.exactS_le_rows (canonicalB_pos hε hε1))).real
      {X | IsSubspaceEmbedding (uniformSparseMatrixOn ι X) U ε} := by
  have hevent : {X : SparseFock.UniformExactS.ExactSample
        (roundedS (failureOrder (Fintype.card κ) δ) ε *
          roundedB (Fintype.card κ) (failureOrder (Fintype.card κ) δ) ε)
        (roundedS (failureOrder (Fintype.card κ) δ) ε) (Fintype.card ι) |
        IsSubspaceEmbedding (uniformSparseMatrixOn ι X) U ε} =
      {X | IsSubspaceEmbedding (SparseFock.UniformExactS.sketchMatrix X)
        (U.reindex (Fintype.equivFin ι) (Fintype.equivFin κ)) ε} := by
    ext X
    exact isSubspaceEmbedding_reindex_equivFin_symm_iff hU _ hε.le
  rw [hevent]
  exact measure_uniformSparse_embedding_success_ge hδ hδ1 hε hε1
    (hU.reindex (Fintype.equivFin ι) (Fintype.equivFin κ))

end NLAlib

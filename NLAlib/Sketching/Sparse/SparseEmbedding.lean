import NLAlib.Sketching.Sparse.MomentMethod.UniformSparseTheorem
import NLAlib.Sketching.Sparse.SparseLaws
/-!
# SparseStack and uniform exact-s subspace embeddings

Both laws give actual probability bounds for `IsSubspaceEmbedding`, with
explicit rounded parameters and exact column sparsity. These are different
distributions; neither theorem assumes a matrix moment bound or operator-band
estimate. Source: manuscript `sh:sparse`, ported sparse-Fock theorem at
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
open SparseSketch

/-- With no coefficient directions, every sketch preserves the zero subspace.
Source: manuscript `sh:sparse`, empty-subspace convention; supports `sparse-ose`. -/
theorem isSubspaceEmbedding_of_isEmpty
    {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ] [IsEmpty κ]
    (S : Matrix ρ ι ℝ) (U : Matrix ι κ ℝ) (ε : ℝ) :
    IsSubspaceEmbedding S U ε := by
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

/-- SparseStack succeeds with probability at least 1-delta under the actual
independent signed-selector law. The rounded sparsity and row count are
bounded by the companion parameter theorem. Source: manuscript `sh:sparse`,
pinned SparseStack matrix theorem; includes d=0.
atlas: sparse-ose -/
theorem measure_sparseStack_embedding_success_ge
    {n d : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U) :
    1 - δ ≤
      (sparseStackMeasure (sparseColumnSparsity (sparseMomentOrder d δ) ε)
        (sparseBlockRows d (sparseMomentOrder d δ) ε) n
        (canonicalB_pos hε hε1)).real
      {z | IsSubspaceEmbedding
        (sparseStackMatrix
          (SparseStackSelectors.toSample z)) U ε} := by
  by_cases hd : d = 0
  · subst d
    have hevent : {z : SparseStackSelectors
        (sparseColumnSparsity (sparseMomentOrder 0 δ) ε)
            (sparseBlockRows 0 (sparseMomentOrder 0 δ) ε) n |
        IsSubspaceEmbedding
        (sparseStackMatrix
          (SparseStackSelectors.toSample z)) U ε} = Set.univ := by
      ext z
      simp [isSubspaceEmbedding_of_isEmpty]
    rw [hevent, probReal_univ]
    linarith
  · have hmain := fully_independent_sparseStack_matrix
      (Nat.one_le_iff_ne_zero.mpr hd) hδ hδ1 hε hε1 U hU
    simpa only [sparseStackMeasure, FiniteLaw.real_toMeasure] using hmain.oseSuccess

/-- SparseStack's actual Gram-error failure probability is at most delta.
Source: manuscript `sh:sparse`, pinned full moment/coupling theorem.
atlas: sparse-ose -/
theorem measure_sparseStack_gram_failure_le
    {n d : ℕ} {δ ε : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U) :
    (sparseStackMeasure (sparseColumnSparsity (sparseMomentOrder d δ) ε)
      (sparseBlockRows d (sparseMomentOrder d δ) ε) n
      (canonicalB_pos hε hε1)).real
      {z | ε < specNorm (Uᵀ *
        ((sparseStackMatrix
            (SparseStackSelectors.toSample z))ᵀ *
          sparseStackMatrix
            (SparseStackSelectors.toSample z) * U) - 1)} ≤ δ := by
  simpa only [sparseStackMeasure, FiniteLaw.real_toMeasure,
    specNorm_eq_norm, sketchGram] using
    (fully_independent_sparseStack_matrix
      hd hδ hδ1 hε hε1 U hU).operatorFailure

/-- Independent uniform signed supports of exactly s rows give an embedding
with probability at least 1-delta under their actual measure, also for d=0.
Source: manuscript `sh:exact-s`, pinned fill/thin coupling theorem.
atlas: sparse-ose -/
theorem measure_uniformSparse_embedding_success_ge
    {n d : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U) :
    1 - δ ≤
      (uniformSparseMeasure
        (sparseColumnSparsity (sparseMomentOrder d δ) ε * sparseBlockRows d (sparseMomentOrder d δ)
            ε)
        (sparseColumnSparsity (sparseMomentOrder d δ) ε) n
        (UniformSparse.le_rows
          (canonicalB_pos hε hε1))).real
      {X | IsSubspaceEmbedding (uniformSparseMatrix X) U ε} := by
  by_cases hd : d = 0
  · subst d
    have hevent : {X : UniformSparseSample
        (sparseColumnSparsity (sparseMomentOrder 0 δ) ε * sparseBlockRows 0 (sparseMomentOrder 0 δ)
            ε)
        (sparseColumnSparsity (sparseMomentOrder 0 δ) ε) n | IsSubspaceEmbedding
        (uniformSparseMatrix X) U ε} = Set.univ := by
      ext X
      simp [isSubspaceEmbedding_of_isEmpty]
    rw [hevent, probReal_univ]
    linarith
  · simpa only [uniformSparseMeasure, FiniteLaw.real_toMeasure] using
      (UniformSparse.matrix_ose_success
        (Nat.one_le_iff_ne_zero.mpr hd) hδ hδ1 hε hε1 U hU)

/-- Uniform exact-s signed supports have the same explicit Gram failure
bound as SparseStack, under their own actual law.
Source: manuscript `sh:exact-s`, pinned exact-s matrix endpoint.
atlas: sparse-ose -/
theorem measure_uniformSparse_gram_failure_le
    {n d : ℕ} {δ ε : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U) :
    (uniformSparseMeasure
      (sparseColumnSparsity (sparseMomentOrder d δ) ε * sparseBlockRows d (sparseMomentOrder d δ) ε)
      (sparseColumnSparsity (sparseMomentOrder d δ) ε) n
      (UniformSparse.le_rows
        (canonicalB_pos hε hε1))).real
      {X | ε < specNorm (Uᵀ * ((uniformSparseMatrix X)ᵀ *
        uniformSparseMatrix X * U) - 1)} ≤ δ := by
  simpa only [uniformSparseMeasure, FiniteLaw.real_toMeasure,
    specNorm_eq_norm, sketchGram] using
    (UniformSparse.matrix_operator_failure
      hd hδ hδ1 hε hε1 U hU)

/-- The rounded sparsity and row count shared by both sparse laws satisfy
s<1356q/epsilon and m<306456(d+q)/epsilon², q=max(1,ceil(log₂(d/delta))).
Source: manuscript `sh:sparse`, pinned rounded integer parameter package.
atlas: sparse-ose -/
theorem sparse_embedding_parameters
    {d : ℕ} {δ ε : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (sparseColumnSparsity (sparseMomentOrder d δ) ε : ℝ) <
        1356 * (sparseMomentOrder d δ : ℝ) / ε ∧
      (sparseRows d (sparseMomentOrder d δ) ε : ℝ) <
        306456 * ((d : ℝ) + sparseMomentOrder d δ) / ε ^ 2 ∧
      2 ≤ sparseBlockRows d (sparseMomentOrder d δ) ε := by
  obtain ⟨_, _, hs, hm, hb⟩ := main_parameter_package (delta := δ) hd hε hε1
  exact ⟨hs, hm, hb⟩

end NLAlib

import NLAlib.Sketching.SparseFock.ExactSparseEmbedding
import NLAlib.Sketching.SparseFrameBridge
import NLAlib.Sketching.SparseLaws

/-!
# SparseStack and uniform exact-s subspace embeddings

Both laws give actual probability bounds for `IsSubspaceEmbedding`, with
explicit rounded parameters and exact column sparsity. These are different
distributions; neither theorem assumes a matrix moment bound or operator-band
estimate. Source: manuscript `sh:sparse`, ported sparse-Fock theorem at
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
open SparseFock.PaperParameters SparseFock.MainTheoremAssembly

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
      (sparseStackMeasure (roundedS (failureOrder d δ) ε)
        (roundedB d (failureOrder d δ) ε) n
        (canonicalB_pos hε hε1)).real
      {z | IsSubspaceEmbedding
        (SparseFock.SparseStackModel.stackMatrix
          (SparseFock.SparseStackDistribution.toSample z)) U ε} := by
  by_cases hd : d = 0
  · subst d
    have hevent : {z : SparseFock.SparseStackDistribution.RawSample
        (roundedS (failureOrder 0 δ) ε) (roundedB 0 (failureOrder 0 δ) ε) n |
        IsSubspaceEmbedding
        (SparseFock.SparseStackModel.stackMatrix
          (SparseFock.SparseStackDistribution.toSample z)) U ε} = Set.univ := by
      ext z
      simp [isSubspaceEmbedding_of_isEmpty]
    rw [hevent, probReal_univ]
    linarith
  · have hmain := SparseFock.MainTheorem.fully_independent_sparseStack_matrix
      (Nat.one_le_iff_ne_zero.mpr hd) hδ hδ1 hε hε1 U hU
    simpa only [sparseStackMeasure, SparseFock.FiniteLaw.real_toMeasure,
      ← isMatrixSparseStackOSE_iff_isSubspaceEmbedding hU] using hmain.oseSuccess

/-- SparseStack's actual Gram-error failure probability is at most delta.
Source: manuscript `sh:sparse`, pinned full moment/coupling theorem.
atlas: sparse-ose -/
theorem measure_sparseStack_gram_failure_le
    {n d : ℕ} {δ ε : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U) :
    (sparseStackMeasure (roundedS (failureOrder d δ) ε)
      (roundedB d (failureOrder d δ) ε) n
      (canonicalB_pos hε hε1)).real
      {z | ε < specNorm (U.transpose *
        (SparseFock.SparseStackModel.sketchGram
          (SparseFock.SparseStackDistribution.toSample z) * U) - 1)} ≤ δ := by
  simpa only [sparseStackMeasure, SparseFock.FiniteLaw.real_toMeasure,
    specNorm_eq_norm] using
    (SparseFock.MainTheorem.fully_independent_sparseStack_matrix
      hd hδ hδ1 hε hε1 U hU).operatorFailure

/-- The uniform exact-s source predicate is the library embedding predicate.
Source: manuscript `sh:exact-s`, coordinate identification; supports `sparse-ose`. -/
theorem isMatrixUniformExactSOSE_iff_isSubspaceEmbedding
    {s b n d : ℕ} {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U)
    (X : SparseFock.UniformExactS.ExactSample (s * b) s n) (ε : ℝ) :
    SparseFock.UniformExactS.IsMatrixUniformExactSOSE U X ε ↔
      IsSubspaceEmbedding (SparseFock.UniformExactS.sketchMatrix X) U ε :=
  (isSubspaceEmbedding_iff_applyRectMatrix_bounds _ hU ε).symm

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
        (roundedS (failureOrder d δ) ε * roundedB d (failureOrder d δ) ε)
        (roundedS (failureOrder d δ) ε) n
        (SparseFock.UniformExactS.exactS_le_rows
          (canonicalB_pos hε hε1))).real
      {X | IsSubspaceEmbedding (SparseFock.UniformExactS.sketchMatrix X) U ε} := by
  by_cases hd : d = 0
  · subst d
    have hevent : {X : SparseFock.UniformExactS.ExactSample
        (roundedS (failureOrder 0 δ) ε * roundedB 0 (failureOrder 0 δ) ε)
        (roundedS (failureOrder 0 δ) ε) n | IsSubspaceEmbedding
        (SparseFock.UniformExactS.sketchMatrix X) U ε} = Set.univ := by
      ext X
      simp [isSubspaceEmbedding_of_isEmpty]
    rw [hevent, probReal_univ]
    linarith
  · simpa only [uniformSparseMeasure, SparseFock.FiniteLaw.real_toMeasure,
      ← isMatrixUniformExactSOSE_iff_isSubspaceEmbedding hU] using
      (SparseFock.UniformExactS.uniformExactS_matrix_ose_success
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
      (roundedS (failureOrder d δ) ε * roundedB d (failureOrder d δ) ε)
      (roundedS (failureOrder d δ) ε) n
      (SparseFock.UniformExactS.exactS_le_rows
        (canonicalB_pos hε hε1))).real
      {X | ε < specNorm (U.transpose *
        (SparseFock.UniformExactS.sketchGram X * U) - 1)} ≤ δ := by
  simpa only [uniformSparseMeasure, SparseFock.FiniteLaw.real_toMeasure,
    specNorm_eq_norm] using
    (SparseFock.UniformExactS.uniformExactS_matrix_operator_failure
      hd hδ hδ1 hε hε1 U hU)

/-- The rounded sparsity and row count shared by both sparse laws satisfy
s<1356q/epsilon and m<306456(d+q)/epsilon², q=max(1,ceil(log₂(d/delta))).
Source: manuscript `sh:sparse`, pinned rounded integer parameter package.
atlas: sparse-ose -/
theorem sparse_embedding_parameters
    {d : ℕ} {δ ε : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (roundedS (failureOrder d δ) ε : ℝ) <
        1356 * (failureOrder d δ : ℝ) / ε ∧
      (roundedM d (failureOrder d δ) ε : ℝ) <
        306456 * ((d : ℝ) + failureOrder d δ) / ε ^ 2 ∧
      2 ≤ roundedB d (failureOrder d δ) ε := by
  obtain ⟨_, _, hs, hm, hb⟩ := main_parameter_package (delta := δ) hd hε hε1
  exact ⟨hs, hm, hb⟩

end NLAlib

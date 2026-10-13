import NLAlib.Sketching.Sparse.SparseEmbedding
/-!
# Sparse embeddings on arbitrary probability spaces

The concrete independent SparseStack and exact-s laws are transported to any
measurable random variable having those laws. No standard Borel assumption on
the original probability space is needed. Source: manuscript `sh:sparse` and
`sh:exact-s`; pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
open MeasureTheory
namespace NLAlib
open SparseSketch

/-- An arbitrary random variable with the actual independent signed-selector
law gives a SparseStack embedding with probability at least 1-delta.
Source: manuscript `sh:sparse`, concrete law transport; includes d=0.
atlas: sparse-ose -/
theorem measure_sparseStack_embedding_success_ge_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U)
    (Z : Ω → SparseStackSelectors
      (sparseColumnSparsity (sparseMomentOrder d δ) ε) (sparseBlockRows d (sparseMomentOrder d δ) ε)
          n)
    (hZ : Measurable Z)
    (hlaw : μ.map Z = sparseStackMeasure (sparseColumnSparsity (sparseMomentOrder d δ) ε)
      (sparseBlockRows d (sparseMomentOrder d δ) ε) n (canonicalB_pos hε hε1)) :
    1 - δ ≤ μ.real {ω | IsSubspaceEmbedding
      (sparseStackMatrix
        (SparseStackSelectors.toSample (Z ω))) U ε} := by
  have hmass := FiniteLaw.real_preimage_of_map_eq_toMeasure
    (sparseStackSelectorLaw
      (sparseColumnSparsity (sparseMomentOrder d δ) ε) (sparseBlockRows d (sparseMomentOrder d δ) ε)
          n
      (canonicalB_pos hε hε1)) Z hZ hlaw
    {z | IsSubspaceEmbedding (sparseStackMatrix
      (SparseStackSelectors.toSample z)) U ε}
  rw [← FiniteLaw.real_toMeasure] at hmass
  change μ.real {ω | IsSubspaceEmbedding
    (sparseStackMatrix
      (SparseStackSelectors.toSample (Z ω))) U ε} = _ at hmass
  rw [hmass]
  exact measure_sparseStack_embedding_success_ge hδ hδ1 hε hε1 hU

/-- An arbitrary random variable with the independent uniform signed exact-s
column law gives an embedding with probability at least 1-delta.
Source: manuscript `sh:exact-s`, concrete law transport; includes d=0.
atlas: sparse-ose -/
theorem measure_uniformSparse_embedding_success_ge_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {U : Matrix (Fin n) (Fin d) ℝ} (hU : HasOrthonormalCols U)
    (X : Ω → UniformSparseSample
      (sparseColumnSparsity (sparseMomentOrder d δ) ε * sparseBlockRows d (sparseMomentOrder d δ) ε)
      (sparseColumnSparsity (sparseMomentOrder d δ) ε) n)
    (hX : Measurable X)
    (hlaw : μ.map X = uniformSparseMeasure
      (sparseColumnSparsity (sparseMomentOrder d δ) ε * sparseBlockRows d (sparseMomentOrder d δ) ε)
      (sparseColumnSparsity (sparseMomentOrder d δ) ε) n
      (UniformSparse.le_rows (canonicalB_pos hε hε1))) :
    1 - δ ≤ μ.real {ω | IsSubspaceEmbedding
      (uniformSparseMatrix (X ω)) U ε} := by
  have hmass := FiniteLaw.real_preimage_of_map_eq_toMeasure
    (uniformSparseSampleLaw
      (UniformSparse.le_rows (canonicalB_pos hε hε1))) X hX hlaw
    {x | IsSubspaceEmbedding (uniformSparseMatrix x) U ε}
  rw [← FiniteLaw.real_toMeasure] at hmass
  change μ.real {ω | IsSubspaceEmbedding
    (uniformSparseMatrix (X ω)) U ε} = _ at hmass
  rw [hmass]
  exact measure_uniformSparse_embedding_success_ge hδ hδ1 hε hε1 hU

end NLAlib

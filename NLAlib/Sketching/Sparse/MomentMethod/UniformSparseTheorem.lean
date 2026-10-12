/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.MomentMethod.UniformSparseRoundedBounds
set_option autoImplicit false

/-!
# Exact-s public matrix embedding theorem

The full explicit parameter package and concrete orthonormal-matrix embedding endpoints.
Ported from `SparseFockFormal.UniformExactSMainTheorem` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLAlib.SparseSketch.UniformSparse

noncomputable section

variable {b s n d : ℕ}

/-! ## Literal vector OSE and the operator-norm event -/

/-- Every conclusion of the canonical uniform signed exact-`s` OSNAP
theorem for a fixed Parseval frame.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure UniformExactSMainConclusions
    {n d : ℕ} (delta eps : ℝ) (F : Frame n d)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (uniformSparseSampleLaw (n := n)
        (le_rows (s := sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps < ‖gramError F (uniformSparseMatrix X)‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (uniformSparseSampleLaw (n := n)
        (le_rows (s := sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsSubspaceEmbedding (uniformSparseMatrix X) (rowMatrix F.u) eps}
  exactColumnSparsity :
    ∀ (X : UniformSparseSample
        (sparseColumnSparsity (sparseMomentOrder d delta) eps *
          sparseBlockRows d (sparseMomentOrder d delta) eps)
        (sparseColumnSparsity (sparseMomentOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (sparseColumnSparsity (sparseMomentOrder d delta) eps *
          sparseBlockRows d (sparseMomentOrder d delta) eps) //
          uniformSparseMatrix X r i ≠ 0} =
        sparseColumnSparsity (sparseMomentOrder d delta) eps
  qAtLeastOne : 1 ≤ sparseMomentOrder d delta
  sparsityStrict :
    (sparseColumnSparsity (sparseMomentOrder d delta) eps : ℝ) <
      1356 * (sparseMomentOrder d delta : ℝ) / eps
  rowsStrict :
    (sparseRows d (sparseMomentOrder d delta) eps : ℝ) <
      306456 * ((d : ℝ) + sparseMomentOrder d delta) / eps ^ 2
  bAtLeastTwo : 2 ≤ sparseBlockRows d (sparseMomentOrder d delta) eps
  rowsFactor :
    sparseRows d (sparseMomentOrder d delta) eps =
      sparseColumnSparsity (sparseMomentOrder d delta) eps *
        sparseBlockRows d (sparseMomentOrder d delta) eps

/-- Hypothesis-free canonical theorem for independent uniform signed exact-`s`
columns.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem main_conclusions
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    UniformExactSMainConclusions delta eps F heps0 heps1 := by
  have hparams := main_parameter_package
    (d := d) (delta := delta) hd heps0 heps1
  rcases hparams with ⟨_hsLower, _hmLower, hsStrict, hmStrict, hbTwo⟩
  refine
    { operatorFailure :=
        rounded_operator_norm_failure_le_delta
          hd hdelta0 hdelta1 heps0 heps1 F
      oseSuccess :=
        rounded_ose_success
          hd hdelta0 hdelta1 heps0 heps1 F
      exactColumnSparsity := ?_
      qAtLeastOne := one_le_sparseMomentOrder d delta
      sparsityStrict := hsStrict
      rowsStrict := hmStrict
      bAtLeastTwo := hbTwo
      rowsFactor := sparseRows_eq_s_mul_b d (sparseMomentOrder d delta) eps }
  intro X i
  exact card_filter_uniformSparseMatrix_ne_zero X
    (sparseColumnSparsity_pos (q := sparseMomentOrder d delta) heps0) i

/-! ## Literal source-matrix form -/

/-- Literal source-matrix operator-norm tail.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_operator_failure
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (uniformSparseSampleLaw (n := n)
        (le_rows (s := sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps <
        ‖U.transpose * (sketchGram (uniformSparseMatrix X) * U) - 1‖} ≤ delta := by
  let F := frameOfMatrix U hU
  simpa [F] using
    (rounded_operator_norm_failure_le_delta
      hd hdelta0 hdelta1 heps0 heps1 F)

/-- Literal source-matrix vector OSE success probability.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_ose_success
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    1 - delta ≤
      (uniformSparseSampleLaw (n := n)
        (le_rows (s := sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsSubspaceEmbedding (uniformSparseMatrix X) U eps} := by
  let F := frameOfMatrix U hU
  simpa [F] using
    (rounded_ose_success
      hd hdelta0 hdelta1 heps0 heps1 F)

end

end NLAlib.SparseSketch.UniformSparse

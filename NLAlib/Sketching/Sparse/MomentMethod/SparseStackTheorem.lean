/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.BandEnvelope
import NLAlib.Sketching.Sparse.MomentMethod.IndependentFrame
import NLAlib.Sketching.Sparse.MomentMethod.FrameOfMatrix
import Mathlib.Tactic


/-!
# Explicit fully independent SparseStack theorem

This is the hypothesis-free endpoint corresponding to TeX Theorem 1.1.  It
is stated first for the exact Parseval-frame model used in the proof and then
for a literal matrix `U` with `Uᵀ U = I`.
-/

namespace NLAlib.SparseSketch

open SparseStackSelectors

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The paper's concrete band proposition, specialized to its rounded integer
parameters.  This is the last operator input formerly present in the
conditional endgame.

Source: ported from `SparseFockFormal.MainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_band_bound
    {n d : ℕ} {delta eps : ℝ}
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (shift : Shift) (nu : ℕ)
    (hnu : nu ≤ 2 * sparseMomentOrder d delta) :
    ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) F
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
      bandEnvelope d (sparseMomentOrder d delta)
        (sparseRows d (sparseMomentOrder d delta) eps)
        (sparseColumnSparsity (sparseMomentOrder d delta) eps) := by
  have hs : 0 < sparseColumnSparsity (sparseMomentOrder d delta) eps := sparseColumnSparsity_pos
      heps0
  have hbTwo : 2 ≤ sparseBlockRows d (sparseMomentOrder d delta) eps :=
    two_le_main_sparseBlockRows (d := d) (delta := delta) heps0 heps1
  have hb : 1 < sparseBlockRows d (sparseMomentOrder d delta) eps := by omega
  rw [sparseRows_eq_s_mul_b]
  exact concrete_band_bound_le_beta F
    (sparseColumnSparsity (sparseMomentOrder d delta) eps)
    (sparseBlockRows d (sparseMomentOrder d delta) eps)
    (sparseMomentOrder d delta) nu hs hb hnu shift

/-- Hypothesis-free fixed-frame form of the full theorem.

Source: ported from `SparseFockFormal.MainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fully_independent_sparseStack
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    MainConclusions delta eps F heps0 heps1 := by
  apply main_conclusions_of_band_bounds hd hdelta0 hdelta1 heps0 heps1 F
  intro shift nu hnu
  exact rounded_band_bound heps0 heps1 F shift nu hnu

/-- Every conclusion of TeX Theorem 1.1 in the source matrix notation.

Source: ported from `SparseFockFormal.MainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure MatrixMainConclusions {n d : ℕ} (delta eps : ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
      {z | eps <
        ‖U.transpose * (sketchGram (sparseStackMatrix (toSample z)) * U) - 1‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
        {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) U eps}
  exactColumnSparsity :
    ∀ (z : SparseStackSelectors (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (sparseColumnSparsity (sparseMomentOrder d delta) eps) ×
            Fin (sparseBlockRows d (sparseMomentOrder d delta) eps) //
          sparseStackMatrix (toSample z) r i ≠ 0} =
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

/-- Literal matrix form of the explicit theorem.

Source: ported from `SparseFockFormal.MainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fully_independent_sparseStack_matrix
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    MatrixMainConclusions delta eps U heps0 heps1 := by
  let F := frameOfMatrix U hU
  have hmain : MainConclusions delta eps F heps0 heps1 :=
    fully_independent_sparseStack hd hdelta0 hdelta1 heps0 heps1 F
  refine
    { operatorFailure := ?_
      oseSuccess := ?_
      exactColumnSparsity := hmain.exactColumnSparsity
      qAtLeastOne := hmain.qAtLeastOne
      sparsityStrict := hmain.sparsityStrict
      rowsStrict := hmain.rowsStrict
      bAtLeastTwo := hmain.bAtLeastTwo
      rowsFactor := hmain.rowsFactor }
  · simpa [F] using hmain.operatorFailure
  · simpa [F] using hmain.oseSuccess

/-- Conditioning corollary for an arbitrary finite law of frames independent
of the fully independent SparseStack sample.

Source: ported from `SparseFockFormal.MainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fully_independent_sparseStack_independent_frame
    {Omega : Type*} [Fintype Omega]
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (frameLaw : FiniteLaw Omega) (frames : Omega → Frame n d) :
    1 - delta ≤
      (FiniteLaw.product frameLaw
        (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
        {outcome | IsSubspaceEmbedding (sparseStackMatrix (toSample outcome.2))
            (rowMatrix (frames outcome.1).u) eps} := by
  apply independent_frame_ose_success_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 frameLaw frames
  intro omega shift nu hnu
  exact rounded_band_bound heps0 heps1 (frames omega) shift nu hnu

end

end NLAlib.SparseSketch

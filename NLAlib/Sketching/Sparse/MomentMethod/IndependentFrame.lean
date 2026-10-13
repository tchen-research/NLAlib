/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.MomentMethod.Assembly
import NLAlib.Sketching.Sparse.FiniteLaw.BinaryProduct
import Mathlib.Tactic


/-!
# Conditioning corollary for a frame independent of the sketch

The fixed-frame theorem is the load-bearing statement.  This module gives a
literal finite product-law formulation of the paper's alternative wording in
which the orthonormal frame is sampled independently of SparseStack.
-/

namespace NLAlib.SparseSketch

open SparseStackSelectors

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Uniform fixed-frame band estimates imply the OSE success bound under the
literal independent product of an arbitrary finite frame law and SparseStack.

Source: ported from `SparseFockFormal.IndependentFrameAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem independent_frame_ose_success_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (frameLaw : FiniteLaw Omega) (frames : Omega → Frame n d)
    (hband : ∀ omega shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) (frames omega)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    1 - delta ≤
      (FiniteLaw.product frameLaw
        (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
        {outcome | IsSubspaceEmbedding (sparseStackMatrix (toSample outcome.2))
            (rowMatrix (frames outcome.1).u) eps} := by
  apply FiniteLaw.le_product_prob
  intro omega
  exact rounded_success_probability_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 (frames omega) (hband omega)

/-- Literal operator-norm tail form for an independently sampled finite
Parseval frame.

Source: ported from `SparseFockFormal.IndependentFrameAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem independent_frame_operator_failure_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (frameLaw : FiniteLaw Omega) (frames : Omega → Frame n d)
    (hband : ∀ omega shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) (frames omega)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    (FiniteLaw.product frameLaw
      (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
      {outcome | eps <
        ‖gramError (frames outcome.1) (sparseStackMatrix (toSample outcome.2))‖} ≤ delta := by
  apply FiniteLaw.product_prob_le
  intro omega
  exact rounded_operator_norm_failure_le_delta_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 (frames omega) (hband omega)

end

end NLAlib.SparseSketch

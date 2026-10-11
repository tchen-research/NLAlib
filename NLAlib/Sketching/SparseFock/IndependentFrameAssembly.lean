/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.EmbeddingAssembly
import NLAlib.ForMathlib.Probability.FiniteProductLaw
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Conditioning corollary for a frame independent of the sketch

The fixed-frame theorem is the load-bearing statement.  This module gives a
literal finite product-law formulation of the paper's alternative wording in
which the orthonormal frame is sampled independently of SparseStack.
-/

namespace NLAlib.SparseFock.IndependentFrameAssembly

open scoped Matrix.Norms.L2Operator
open ParsevalFrame SparseStackModel SparseStackDistribution
open PaperParameters ConcreteLadder FiniteHilbert MainTheoremAssembly

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
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) (frames omega)
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    1 - delta ≤
      (FiniteLaw.product frameLaw
        (rawSampleLaw (roundedS (failureOrder d delta) eps)
          (roundedB d (failureOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
        {outcome | MatrixTail.IsSparseStackOSE (frames outcome.1)
          (toSample outcome.2) eps} := by
  apply FiniteLaw.le_product_prob
  intro omega
  exact ConcreteMomentEndgame.rounded_success_probability_of_band_bounds
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
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) (frames omega)
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    (FiniteLaw.product frameLaw
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
      {outcome | eps <
        ‖gramError (frames outcome.1) (toSample outcome.2)‖} ≤ delta := by
  apply FiniteLaw.product_prob_le
  intro omega
  exact ConcreteMomentEndgame.rounded_operator_norm_failure_le_delta_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 (frames omega) (hband omega)

end

end NLAlib.SparseFock.IndependentFrameAssembly

/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.IIDComparison.MomentTransfer
import NLAlib.Sketching.Sparse.Bands.LadderIteration
import NLAlib.Sketching.Sparse.MomentMethod.GramTail
import Mathlib.Tactic


/-!
# Concrete moment and Markov endgame

This module joins the proved convex-order distribution transfer, the exact
vacuum identity, the concrete ladder iteration, and the finite-law matrix
Markov inequality.  Its sole remaining input is the displayed restricted
norm bound for the actual three normalized bands.
-/

namespace NLAlib.SparseSketch

open SparseStackSelectors

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {s b n d : ℕ}

/-- The literal SparseStack trace moment is bounded by the concrete iid
ladder estimate, including the exact coupling factor `c_b^(4q)`.

Source: ported from `SparseFockFormal.ConcreteMomentEndgame`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem raw_trace_moment_le_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b delta *
        gradeProjection (d := d) nu‖ ≤ beta) :
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) ≤
      (d : ℝ) * (3 * cB b ^ 2 * beta) ^ (2 * q) := by
  have htransfer := raw_trace_moment_le_scaled_product hs hb F q
  have hiid := iid_trace_moment_le_of_band_bounds
    (m := s * b) hb F hbeta hband
  have hcB0 : 0 ≤ cB b :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_cB (lt_trans Nat.zero_lt_one hb))
  calc
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) ≤
        cB b ^ (4 * q) *
          (iidLaw b hb (s * b) n).expect
            (fun omega ↦ Matrix.trace
              ((iidGramError b F omega) ^ (2 * q))) := htransfer
    _ ≤ cB b ^ (4 * q) *
        ((d : ℝ) * (3 * beta) ^ (2 * q)) := by
      exact mul_le_mul_of_nonneg_left hiid (pow_nonneg hcB0 _)
    _ = (d : ℝ) * (3 * cB b ^ 2 * beta) ^ (2 * q) := by
      have hc : cB b ^ (4 * q) = (cB b ^ 2) ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hc]
      calc
        (cB b ^ 2) ^ (2 * q) *
            ((d : ℝ) * (3 * beta) ^ (2 * q)) =
            (d : ℝ) * ((cB b ^ 2) ^ (2 * q) *
              (3 * beta) ^ (2 * q)) := by ring
        _ = (d : ℝ) * ((cB b ^ 2) * (3 * beta)) ^ (2 * q) := by
          congr 1
          exact (mul_pow (cB b ^ 2) (3 * beta) (2 * q)).symm
        _ = (d : ℝ) * (3 * cB b ^ 2 * beta) ^ (2 * q) := by
          congr 2
          ring

/-- The exact finite-law Markov tail resulting from the concrete band
estimate.

Source: ported from `SparseFockFormal.ConcreteMomentEndgame`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_failure_tail_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} (hq : 0 < q) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b delta *
        gradeProjection (d := d) nu‖ ≤ beta)
    {eps : ℝ} (heps : 0 < eps) :
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).prob
        {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} ≤
      (d : ℝ) * ((3 * cB b ^ 2 * beta) / eps) ^ (2 * q) := by
  have hmarkov := sparseStack_ose_failure_tail
    (s := s) (lt_trans Nat.zero_lt_one hb) F q hq eps heps
  have hmoment := raw_trace_moment_le_of_band_bounds hs hb F hbeta hband
  calc
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).prob
        {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} ≤
        (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
          (fun z ↦ ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
            eps ^ (2 * q) := hmarkov
    _ ≤ ((d : ℝ) * (3 * cB b ^ 2 * beta) ^ (2 * q)) /
          eps ^ (2 * q) := by
      exact div_le_div_of_nonneg_right hmoment (pow_nonneg heps.le _)
    _ = (d : ℝ) * ((3 * cB b ^ 2 * beta) / eps) ^ (2 * q) := by
      rw [div_pow]
      ring

/-- All scalar constants, rounding, and the base-two failure order are now
discharged.  Supplying the actual rounded band envelope gives the paper's
failure probability `≤ delta`.

Source: ported from `SparseFockFormal.ConcreteMomentEndgame`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_failure_le_delta_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) F
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (by
          have h := two_le_main_sparseBlockRows
            (d := d) (delta := delta) heps0 heps1
          omega : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps)).prob
      {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} ≤ delta := by
  let q := sparseMomentOrder d delta
  let s := sparseColumnSparsity q eps
  let b := sparseBlockRows d q eps
  let beta := bandEnvelope d q (sparseRows d q eps) s
  have hq : 0 < q := Nat.zero_lt_of_lt (one_le_sparseMomentOrder d delta)
  have hs : 0 < s := by
    simpa [s, q] using sparseColumnSparsity_pos (q := sparseMomentOrder d delta) heps0
  have hbTwo : 2 ≤ b := by
    simpa [b, q] using two_le_main_sparseBlockRows
      (d := d) (delta := delta) heps0 heps1
  have hb : 1 < b := lt_of_lt_of_le (by omega) hbTwo
  have hm : (0 : ℝ) < sparseRows d q eps := by
    rw [sparseRows]
    positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbeta0 : 0 ≤ beta := by
    exact bandEnvelope_nonneg hm hsR
  have hband' : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift * gradeProjection (d := d) nu‖ ≤ beta := by
    intro shift nu hnu
    dsimp [q, s, b, beta]
    exact hband shift nu hnu
  have htail := sparseStack_failure_tail_of_band_bounds
    (s := s) (b := b) hs hb F hq hbeta0 hband' heps0
  have hcB0 : 0 ≤ cB b :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_cB (lt_trans Nat.zero_lt_one hb))
  have hcBStar : cB b ≤ convexOrderConstant :=
    cB_le_cStar (lt_trans Nat.zero_lt_one hb)
  have hcSq : cB b ^ 2 ≤ convexOrderConstant ^ 2 := by
    nlinarith [convexOrderConstant_pos]
  have hbase0 : 0 ≤ 3 * cB b ^ 2 * beta / eps := by positivity
  have hbase : 3 * cB b ^ 2 * beta / eps ≤
      momentBase d q eps := by
    rw [momentBase]
    apply div_le_div_of_nonneg_right _ heps0.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcSq (by norm_num)) hbeta0
  have hpow : (3 * cB b ^ 2 * beta / eps) ^ (2 * q) ≤
      (momentBase d q eps) ^ (2 * q) :=
    pow_le_pow_left₀ hbase0 hbase _
  calc
    (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (by
          have h := two_le_main_sparseBlockRows
            (d := d) (delta := delta) heps0 heps1
          omega : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps)).prob
      {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} =
        (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).prob
          {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} := by
            simp [s, b, q]
    _ ≤ (d : ℝ) * (3 * cB b ^ 2 * beta / eps) ^ (2 * q) := htail
    _ ≤ (d : ℝ) * (momentBase d q eps) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ delta := by
      simpa [q] using rounded_scalar_failure_le_delta
        hd hdelta0 hdelta1 heps0 heps1

/-- The same rounded conclusion in the literal operator-norm form displayed
in the main theorem of the paper.

Source: ported from `SparseFockFormal.ConcreteMomentEndgame`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_operator_norm_failure_le_delta_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) F
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (by
          have h := two_le_main_sparseBlockRows
            (d := d) (delta := delta) heps0 heps1
          omega : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps)).prob
      {z | eps < ‖gramError F (sparseStackMatrix (toSample z))‖} ≤ delta := by
  have hevent :
      {z : SparseStackSelectors (sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) n |
        eps < ‖gramError F (sparseStackMatrix (toSample z))‖} =
      {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} := by
    ext z
    have hiff := norm_gramError_le_iff_isSubspaceEmbedding F (sparseStackMatrix (toSample z))
        heps0.le
    simpa [not_le] using not_congr hiff
  rw [hevent]
  exact rounded_failure_le_delta_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 F hband

/-- Equivalent success-probability form of the rounded theorem.

Source: ported from `SparseFockFormal.ConcreteMomentEndgame`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_success_probability_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) F
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    1 - delta ≤
      (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (by
          have h := two_le_main_sparseBlockRows
            (d := d) (delta := delta) heps0 heps1
          omega : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps)).prob
        {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} := by
  let hbpos : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps := by
    have h := two_le_main_sparseBlockRows
      (d := d) (delta := delta) heps0 heps1
    omega
  let mu := sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
    (sparseBlockRows d (sparseMomentOrder d delta) eps) n hbpos
  let good : Set (SparseStackSelectors (sparseColumnSparsity (sparseMomentOrder d delta) eps)
      (sparseBlockRows d (sparseMomentOrder d delta) eps) n) :=
    {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps}
  have hgoodCompl : goodᶜ =
      {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} := by
    ext z
    rfl
  have hfail : mu.prob goodᶜ ≤ delta := by
    rw [hgoodCompl]
    simpa [mu] using rounded_failure_le_delta_of_band_bounds
      hd hdelta0 hdelta1 heps0 heps1 F hband
  calc
    1 - delta ≤ 1 - mu.prob goodᶜ := sub_le_sub_left hfail 1
    _ = mu.prob good := by
      simpa using (FiniteLaw.prob_compl mu goodᶜ).symm
    _ = (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (by
          have h := two_le_main_sparseBlockRows
            (d := d) (delta := delta) heps0 heps1
          omega : 0 < sparseBlockRows d (sparseMomentOrder d delta) eps)).prob
        {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps} := by
      rfl

end

end NLAlib.SparseSketch

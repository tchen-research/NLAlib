/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.SparseFock.ExactMomentTransfer
import NLAlib.Sketching.Sparse.SparseFock.FullyIndependentSparseStack
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact-s subspace projection tail

Trace-moment failure tails for the uniform exact-`s` Gram error and embedding event.
Ported from `SparseFockFormal.UniformExactSMainTheorem` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLAlib.SparseFock.UniformExactS

open ParsevalFrame SparseIIDCoupling ProductFock VacuumMoment
open ConcreteLadder FiniteHilbert PaperParameters

noncomputable section

variable {b s n d : ℕ}

/-! ## Finite-law Markov endpoint -/

/-- Matrix Markov inequality under the literal independent-column exact-`s`
law.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_matrix_markov_tail
    (hb : 0 < b) (F : Frame n d) (q : ℕ) (hq : 0 < q)
    (eps : ℝ) (heps : 0 < eps) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | eps ≤ ‖gramError F (sketchMatrix X)‖} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F (sketchMatrix X)) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  exact MatrixTail.matrix_markov_tail
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb))
    (fun X ↦ gramError F (sketchMatrix X))
    (fun X ↦ gramError_isHermitian F (sketchMatrix X)) q hq eps heps

/-- Failure of the literal vector OSE property obeys the same trace-moment
tail.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_ose_failure_tail
    (hb : 0 < b) (F : Frame n d) (q : ℕ) (hq : 0 < q)
    (eps : ℝ) (heps : 0 < eps) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | ¬ IsSubspaceEmbedding (sketchMatrix X) (rowMatrix F.u) eps} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F (sketchMatrix X)) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  calc
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | ¬ IsSubspaceEmbedding (sketchMatrix X) (rowMatrix F.u) eps} ≤
        (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
          {X | eps ≤ ‖gramError F (sketchMatrix X)‖} := by
      apply FiniteLaw.prob_mono
      intro X hbad
      by_contra htail
      exact hbad ((norm_gramError_le_iff_isSubspaceEmbedding F (sketchMatrix X) heps.le).mp (not_le.mp htail).le)
    _ ≤ (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F (sketchMatrix X)) ^ (2 * q)).trace) /
        eps ^ (2 * q) :=
      uniformExactS_matrix_markov_tail hb F q hq eps heps

/-! ## Finite-Fock moment endgame -/

/-- The exact-`s` trace moment is bounded by the same concrete ladder
estimate, with the genuine coupling scale in place of `cB`.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactS_trace_moment_le_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb))).expect
        (fun X => ((gramError F (sketchMatrix X)) ^ (2 * q)).trace) ≤
      (d : ℝ) *
        (3 * exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ 2 * beta) ^
          (2 * q) := by
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  let scale := exactScale (s := s) hb0
  have htransfer := exactS_trace_moment_le_scaled_product hs hb F q
  have hiid := ConcreteLadderIteration.iid_trace_moment_le_of_band_bounds
    (m := s * b) hb F hbeta hband
  have hscale0 : 0 ≤ scale := by
    dsimp [scale, exactScale]
    exact (inv_pos.mpr (couplingA_pos hb0 hs)).le
  calc
    _ ≤ scale ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) :=
      htransfer
    _ ≤ scale ^ (4 * q) *
        ((d : ℝ) * (3 * beta) ^ (2 * q)) := by
      exact mul_le_mul_of_nonneg_left hiid (pow_nonneg hscale0 _)
    _ = (d : ℝ) * (3 * scale ^ 2 * beta) ^ (2 * q) := by
      have hpow : scale ^ (4 * q) = (scale ^ 2) ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow]
      calc
        (scale ^ 2) ^ (2 * q) * ((d : ℝ) * (3 * beta) ^ (2 * q)) =
            (d : ℝ) * ((scale ^ 2) ^ (2 * q) *
              (3 * beta) ^ (2 * q)) := by ring
        _ = (d : ℝ) * ((scale ^ 2) * (3 * beta)) ^ (2 * q) := by
          congr 1
          exact (mul_pow (scale ^ 2) (3 * beta) (2 * q)).symm
        _ = (d : ℝ) * (3 * scale ^ 2 * beta) ^ (2 * q) := by
          congr 2
          ring

/-- Markov tail after the concrete band estimate.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_failure_tail_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} (hq : 0 < q) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta)
    {eps : ℝ} (heps : 0 < eps) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb))).prob
        {X | ¬ IsSubspaceEmbedding (sketchMatrix X) (rowMatrix F.u) eps} ≤
      (d : ℝ) *
        ((3 * exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ 2 * beta) /
          eps) ^ (2 * q) := by
  have hmarkov := uniformExactS_ose_failure_tail
    (s := s) (lt_trans Nat.zero_lt_one hb) F q hq eps heps
  have hmoment := exactS_trace_moment_le_of_band_bounds
    (n := n) hs hb F hbeta hband
  calc
    _ ≤ (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb))).expect
          (fun X => ((gramError F (sketchMatrix X)) ^ (2 * q)).trace) /
        eps ^ (2 * q) := hmarkov
    _ ≤ ((d : ℝ) *
          (3 * exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ 2 * beta) ^
            (2 * q)) / eps ^ (2 * q) := by
      exact div_le_div_of_nonneg_right hmoment (pow_nonneg heps.le _)
    _ = (d : ℝ) *
        ((3 * exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ 2 * beta) /
          eps) ^ (2 * q) := by
      rw [div_pow]
      ring

/-! ## Canonical rounded parameters -/

end

end NLAlib.SparseFock.UniformExactS

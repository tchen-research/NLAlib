/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.UniformExactSTransfer
import NLAlib.Sketching.SparseFock.ConcreteLadderIteration
import NLAlib.Sketching.SparseFock.SparseEmbedding
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact-s subspace projection tail

The literal sketch action, Gram distortion equivalences, and trace-moment failure tails.
Ported from `SparseFockFormal.UniformExactSMainTheorem` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLAlib.SparseFock.UniformExactS

open ParsevalFrame SparseIIDCoupling ProductFock VacuumMoment
open ConcreteLadder FiniteHilbert PaperParameters

noncomputable section

variable {b s n d : ℕ}

/-! ## Literal vector OSE and the operator-norm event -/

/-- The vector produced by the uniform exact-`s` sketch after Parseval-frame
analysis.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def exactSVector (F : Frame n d) (X : ExactSample (s * b) s n)
    (x : EVec d) : EuclideanSpace ℝ (Fin (s * b)) :=
  MatrixTail.applyRectMatrix (sketchMatrix X * rowMatrix F.u) x

/-- Literal two-sided squared-norm OSE property for a uniform exact-`s`
outcome.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def IsUniformExactSOSE (F : Frame n d) (X : ExactSample (s * b) s n)
    (eps : ℝ) : Prop :=
  ∀ x : EVec d,
    (1 - eps) * ‖x‖ ^ 2 ≤ ‖exactSVector F X x‖ ^ 2 ∧
      ‖exactSVector F X x‖ ^ 2 ≤ (1 + eps) * ‖x‖ ^ 2

/-- The embedded exact-`s` Gram quadratic form is the squared norm of the
literal sketched vector.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem embeddedGram_quadraticForm (F : Frame n d)
    (X : ExactSample (s * b) s n) (x : EVec d) :
    MatrixTail.quadraticForm (embeddedGram F X) x =
      ‖exactSVector F X x‖ ^ 2 := by
  have hgram : embeddedGram F X =
      (sketchMatrix X * rowMatrix F.u).transpose *
        (sketchMatrix X * rowMatrix F.u) := by
    simp [embeddedGram, sketchGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hgram]
  exact MatrixTail.quadraticForm_transpose_mul_self
    (sketchMatrix X * rowMatrix F.u) x

/-- The generic Gram-OSE predicate agrees with the literal exact-`s` vector
property.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem isGramOSE_embeddedGram_iff_uniformExactSOSE
    (F : Frame n d) (X : ExactSample (s * b) s n) (eps : ℝ) :
    MatrixTail.IsGramOSE (embeddedGram F X) eps ↔
      IsUniformExactSOSE F X eps := by
  constructor <;> intro h x
  · simpa only [embeddedGram_quadraticForm F X x] using h x
  · simpa only [embeddedGram_quadraticForm F X x] using h x

/-- Exact deterministic equivalence between operator-norm control and the
two-sided vector OSE property.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_norm_le_iff_uniformExactSOSE
    (F : Frame n d) (X : ExactSample (s * b) s n)
    (eps : ℝ) (heps : 0 ≤ eps) :
    ‖gramError F X‖ ≤ eps ↔ IsUniformExactSOSE F X eps := by
  rw [show gramError F X = embeddedGram F X - 1 by rfl]
  rw [MatrixTail.gramError_norm_le_iff_isGramOSE
    (embeddedGram F X) (embeddedGram_isHermitian F X) eps heps]
  exact isGramOSE_embeddedGram_iff_uniformExactSOSE F X eps

/-! ## Finite-law Markov endpoint -/

/-- Matrix Markov inequality under the literal independent-column exact-`s`
law.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_matrix_markov_tail
    (hb : 0 < b) (F : Frame n d) (q : ℕ) (hq : 0 < q)
    (eps : ℝ) (heps : 0 < eps) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | eps ≤ ‖gramError F X‖} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  exact MatrixTail.matrix_markov_tail
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb))
    (gramError F) (gramError_isHermitian F) q hq eps heps

/-- Failure of the literal vector OSE property obeys the same trace-moment
tail.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_ose_failure_tail
    (hb : 0 < b) (F : Frame n d) (q : ℕ) (hq : 0 < q)
    (eps : ℝ) (heps : 0 < eps) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | ¬ IsUniformExactSOSE F X eps} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  calc
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
        {X | ¬ IsUniformExactSOSE F X eps} ≤
        (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).prob
          {X | eps ≤ ‖gramError F X‖} := by
      apply FiniteLaw.prob_mono
      intro X hbad
      by_contra htail
      exact hbad ((gramError_norm_le_iff_uniformExactSOSE
        F X eps heps.le).mp (not_le.mp htail).le)
    _ ≤ (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
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
        (fun X => ((gramError F X) ^ (2 * q)).trace) ≤
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
        {X | ¬ IsUniformExactSOSE F X eps} ≤
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
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
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

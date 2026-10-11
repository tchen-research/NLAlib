/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.FiniteLocalMoments
import NLAlib.Sketching.SparseFock.ExactSparseEmbedding
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Whole-column limited independence for uniform exact-s OSNAP

The primitive coordinate in this module is one complete signed exact-`s`
column.  Thus a law on `ExactSample (s * b) s n` is `4q`-wise independent
at whole-column granularity precisely when it satisfies `MatchesUpTo` through
order `4q` against `exactSampleLaw`.

Pointwise hollowness makes each scalar Gram-error entry an additive sum of
observables depending on two columns.  Multiplication of matrix entries adds
local interaction degrees, so the trace of the `2q`-th power has degree at
most `4q`.  Exact marginal matching therefore preserves that trace moment,
with no independence premise used inside the algebraic word count.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLAlib.SparseFock.UniformExactS

open ParsevalFrame FiniteLocalMoments
open FiniteLocalMoments.HasLocalDegree
open SparseIIDCoupling ConcreteLadder FiniteHilbert PaperParameters
open MainTheoremAssembly

noncomputable section

variable {b s n d : ℕ}

/-- One row-inner-product summand depends on the two whole columns named by
`i` and `j`.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem columnInner_hasLocalDegree_two
    (i j : Fin n) :
    HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) 2
      (fun X : ExactSample (s * b) s n =>
        ∑ r, columnValue (X i) r * columnValue (X j) r) := by
  apply HasLocalDegree.atom {i, j} _
  · simpa using (Finset.card_insert_le i ({j} : Finset (Fin n)))
  · intro X X' hagree
    have hi : X i = X' i := hagree i (by simp)
    have hj : X j = X' j := hagree j (by simp)
    change (∑ r, columnValue (X i) r * columnValue (X j) r) =
      ∑ r, columnValue (X' i) r * columnValue (X' j) r
    rw [hi, hj]

/-- Every scalar entry of the pointwise exact-`s` Gram error has whole-column
interaction degree at most two.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_entry_hasLocalDegree_two
    (hs : 0 < s) (F : Frame n d) (a c : Fin d) :
    HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) 2
      (fun X : ExactSample (s * b) s n => gramError F X a c) := by
  have hterm (i j : Fin n) :
      HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) 2
        (fun X : ExactSample (s * b) s n =>
          (∑ r, columnValue (X i) r * columnValue (X j) r) *
            F.u i a * F.u j c) := by
    have h := columnInner_hasLocalDegree_two (b := b) (s := s) i j
    have hscaled := HasLocalDegree.smul (F.u i a * F.u j c) h
    convert hscaled using 1
    funext X
    ring
  have hsum :
      HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) 2
        (fun X : ExactSample (s * b) s n =>
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            (∑ r, columnValue (X i) r * columnValue (X j) r) *
              F.u i a * F.u j c) := by
    apply HasLocalDegree.sum_fintype
    intro i
    apply HasLocalDegree.sum_finset (Finset.univ.erase i)
      (fun j X =>
        (∑ r, columnValue (X i) r * columnValue (X j) r) *
          F.u i a * F.u j c)
    intro j _hj
    exact hterm i j
  have hscaled := HasLocalDegree.smul (1 / (s : ℝ)) hsum
  apply HasLocalDegree.congr hscaled
  funext X
  have hhollow := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A a c)
    (gramError_eq_hollow F X hs)
  simpa [hollowGram] using hhollow.symm

/-- An entry of the `r`-th exact-`s` Gram-error power has whole-column
interaction degree at most `2r`.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_pow_entry_hasLocalDegree
    (hs : 0 < s) (F : Frame n d) (r : ℕ) (a c : Fin d) :
    HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) (2 * r)
      (fun X : ExactSample (s * b) s n => ((gramError F X) ^ r) a c) := by
  induction r generalizing a c with
  | zero =>
      simpa using
        (HasLocalDegree.constant (ι := Fin n)
          (α := ExactColumn (s * b) s) 0
          ((1 : Matrix (Fin d) (Fin d) ℝ) a c))
  | succ r ihr =>
      have hsum :
          HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s)
            (2 * r + 2)
            (fun X : ExactSample (s * b) s n =>
              ∑ x : Fin d,
                ((gramError F X) ^ r) a x * gramError F X x c) := by
        apply HasLocalDegree.sum_fintype
        intro x
        exact HasLocalDegree.mul (ihr a x)
          (gramError_entry_hasLocalDegree_two (b := b) hs F x c)
      have hdegree :
          HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s)
            (2 * (Nat.succ r))
            (fun X : ExactSample (s * b) s n =>
              ∑ x : Fin d,
                ((gramError F X) ^ r) a x * gramError F X x c) := by
        simpa [Nat.mul_succ] using hsum
      apply HasLocalDegree.congr hdegree
      funext X
      rw [pow_succ, Matrix.mul_apply]

/-- The `r`-th trace-power observable has whole-column interaction degree at
most `2r`.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_power_hasLocalDegree
    (hs : 0 < s) (F : Frame n d) (r : ℕ) :
    HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) (2 * r)
      (fun X : ExactSample (s * b) s n => ((gramError F X) ^ r).trace) := by
  have hsum :
      HasLocalDegree (ι := Fin n) (α := ExactColumn (s * b) s) (2 * r)
        (fun X : ExactSample (s * b) s n =>
          ∑ a : Fin d, ((gramError F X) ^ r) a a) := by
    apply HasLocalDegree.sum_fintype
    intro a
    exact gramError_pow_entry_hasLocalDegree (b := b) hs F r a a
  apply HasLocalDegree.congr hsum
  funext X
  rfl

/-- **Exact `4q`-wise whole-column moment transfer.**  Marginal matching
through `4q` complete exact-`s` columns preserves the `2q` trace moment
exactly.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_even_moment_eq_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d) (q : ℕ)
    (μ : FiniteLaw (ExactSample (s * b) s n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)) (4 * q)) :
    μ.expect (fun X => ((gramError F X) ^ (2 * q)).trace) =
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
        (fun X => ((gramError F X) ^ (2 * q)).trace) := by
  apply HasLocalDegree.expect_eq_of_matchesUpTo hmatch
  have hdegree : 2 * (2 * q) = 4 * q := by omega
  simpa only [hdegree] using
    (trace_power_hasLocalDegree (b := b) hs F (2 * q))

/-- Matrix Markov under a `4q`-wise matching whole-column law, with the
right-hand side replaced by the fully independent exact-`s` moment.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_markov_tail_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d)
    (q : ℕ) (hq : 0 < q) (eps : ℝ) (heps : 0 < eps)
    (μ : FiniteLaw (ExactSample (s * b) s n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)) (4 * q)) :
    μ.prob {X | eps ≤ ‖gramError F X‖} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  have htail := MatrixTail.matrix_markov_tail μ
    (gramError F) (gramError_isHermitian F) q hq eps heps
  rw [trace_even_moment_eq_of_matchesUpTo_four_mul hs hb F q μ hmatch] at htail
  exact htail

/-- Literal OSE-failure form of the whole-column limited-independence
endpoint.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ose_failure_tail_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d)
    (q : ℕ) (hq : 0 < q) (eps : ℝ) (heps : 0 < eps)
    (μ : FiniteLaw (ExactSample (s * b) s n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)) (4 * q)) :
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤
      (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  calc
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤
        μ.prob {X | eps ≤ ‖gramError F X‖} := by
      apply FiniteLaw.prob_mono
      intro X hbad
      by_contra htail
      exact hbad ((gramError_norm_le_iff_uniformExactSOSE
        F X eps heps.le).mp (not_le.mp htail).le)
    _ ≤ (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => ((gramError F X) ^ (2 * q)).trace) /
        eps ^ (2 * q) :=
      matrix_markov_tail_of_matchesUpTo_four_mul
        hs hb F q hq eps heps μ hmatch

/-! ## Reuse of the independent exact-s moment endpoint -/

/-- The concrete independent-column sparse-Fock moment estimate applies
unchanged to a law matching whole-column marginals through `4q`.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem limited_failure_tail_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} (hq : 0 < q) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta)
    {eps : ℝ} (heps : 0 < eps)
    (μ : FiniteLaw (ExactSample (s * b) s n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb))) (4 * q)) :
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤
      (d : ℝ) *
        ((3 * exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ 2 * beta) /
          eps) ^ (2 * q) := by
  have hmarkov := ose_failure_tail_of_matchesUpTo_four_mul
    hs (lt_trans Nat.zero_lt_one hb) F q hq eps heps μ hmatch
  have hmoment := exactS_trace_moment_le_of_band_bounds
    (n := n) hs hb F hbeta hband
  calc
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤
        (exactSampleLaw (n := n)
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

/-- **Canonical whole-column limited-independence exact-`s` theorem.**  At
the rounded Nelson--Nguyen parameters, matching every marginal of at most
`4 * failureOrder d delta` complete columns gives the same OSE failure
bound `≤ delta` as fully independent exact-`s` columns.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_ose_failure_le_delta_of_matchesUpTo
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (μ : FiniteLaw
      (ExactSample
        (roundedS (failureOrder d delta) eps *
          roundedB d (failureOrder d delta) eps)
        (roundedS (failureOrder d delta) eps) n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)))
      (4 * failureOrder d delta)) :
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤ delta := by
  let q := failureOrder d delta
  let s := roundedS q eps
  let b := roundedB d q eps
  let beta := betaEnvelope d q (roundedM d q eps) s
  have hq : 0 < q := Nat.zero_lt_of_lt (one_le_failureOrder d delta)
  have hs : 0 < s := by
    simpa [s, q] using roundedS_pos (q := failureOrder d delta) heps0
  have hbTwo : 2 ≤ b := by
    simpa [b, q] using two_le_main_roundedB
      (d := d) (delta := delta) heps0 heps1
  have hb : 1 < b := lt_of_lt_of_le (by omega) hbTwo
  have hm : (0 : ℝ) < roundedM d q eps := by
    rw [roundedM]
    positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbeta0 : 0 ≤ beta := betaEnvelope_nonneg hm hsR
  have hband : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta := by
    intro shift nu hnu
    dsimp [q, s, b, beta]
    exact MainTheorem.rounded_band_bound
      (d := d) (delta := delta) heps0 heps1 F shift nu hnu
  have hmatch' : MatchesUpTo μ
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb)))
      (4 * q) := by
    simpa [q, s, b] using hmatch
  have htail := limited_failure_tail_of_band_bounds
    (n := n) hs hb F hq hbeta0 hband heps0 μ hmatch'
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  let scale := exactScale (s := s) hb0
  have hscale0 : 0 ≤ scale := by
    exact (inv_pos.mpr (couplingA_pos hb0 hs)).le
  have hscaleStar : scale ≤ cStar := by
    exact exactScale_le_cStar hb0 hs
  have hscaleSq : scale ^ 2 ≤ cStar ^ 2 := by
    nlinarith [cStar_pos]
  have hbase0 : 0 ≤ 3 * scale ^ 2 * beta / eps := by positivity
  have hbase : 3 * scale ^ 2 * beta / eps ≤
      roundedMomentBase d q eps := by
    rw [roundedMomentBase]
    apply div_le_div_of_nonneg_right _ heps0.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscaleSq (by norm_num)) hbeta0
  have hpow : (3 * scale ^ 2 * beta / eps) ^ (2 * q) ≤
      (roundedMomentBase d q eps) ^ (2 * q) :=
    pow_le_pow_left₀ hbase0 hbase _
  calc
    μ.prob {X | ¬ IsUniformExactSOSE F X eps} ≤
        (d : ℝ) * (3 * scale ^ 2 * beta / eps) ^ (2 * q) := by
      simpa [scale, hb0] using htail
    _ ≤ (d : ℝ) * (roundedMomentBase d q eps) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ delta := by
      simpa [q] using rounded_scalar_failure_le_delta
        hd hdelta0 hdelta1 heps0 heps1

/-- Operator-norm form of the canonical whole-column limited-independence
theorem.

Source: ported from `SparseFockFormal.UniformExactSLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_operator_norm_failure_le_delta_of_matchesUpTo
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (μ : FiniteLaw
      (ExactSample
        (roundedS (failureOrder d delta) eps *
          roundedB d (failureOrder d delta) eps)
        (roundedS (failureOrder d delta) eps) n))
    (hmatch : MatchesUpTo μ
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)))
      (4 * failureOrder d delta)) :
    μ.prob {X | eps < ‖gramError F X‖} ≤ delta := by
  have hevent :
      {X : ExactSample
          (roundedS (failureOrder d delta) eps *
            roundedB d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps) n |
        eps < ‖gramError F X‖} =
      {X | ¬ IsUniformExactSOSE F X eps} := by
    ext X
    have hiff := gramError_norm_le_iff_uniformExactSOSE F X eps heps0.le
    simpa [not_le] using not_congr hiff
  rw [hevent]
  exact rounded_ose_failure_le_delta_of_matchesUpTo
    hd hdelta0 hdelta1 heps0 heps1 F μ hmatch

end

end NLAlib.SparseFock.UniformExactS

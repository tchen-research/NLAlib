/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.FiniteLocalMoments
import NLAlib.Sketching.SparseFock.ConcreteMomentEndgame
import NLAlib.Sketching.SparseFock.MatrixTail
import NLAlib.Sketching.SparseFock.SparseEmbedding
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Limited-independence transfer for SparseStack

The primitive random variables in SparseStack are the *combined* selectors
`Z_(g,i) = (h_g(i), sigma_(g,i))`.  This module proves, without a generator
assumption, that exact `4q`-coordinate marginal agreement with the fully
independent selector law preserves the `2q` trace moment exactly.

The proof is a checked degree argument.  The pointwise hollow Gram identity
makes each Gram-error entry an additive sum of terms depending on two
combined selectors.  Matrix multiplication adds local interaction degrees,
so an entry of the `r`-th matrix power has degree at most `2r`, and its trace
has the same degree.  Taking `r = 2q` gives the advertised `4q` count.

The final theorems apply finite-law matrix Markov directly to an arbitrary
law satisfying this marginal premise.  No polynomial hash construction or
seed-length claim is asserted here: those are separate generator facts, not
needed for the distributional theorem formalized below.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseFock

namespace SparseStackLimitedIndependence

open ParsevalFrame SparseStackModel SparseStackDistribution
open FiniteLocalMoments FiniteLocalMoments.HasLocalDegree
open SparseIIDCoupling ConcreteLadder FiniteHilbert
open ConcreteMomentEndgame
open PaperParameters MainTheoremAssembly

noncomputable section

variable {s b n d : ℕ}

/-- The inner product belonging to one hollow Gram summand depends on only
the two combined selectors indexed by `(g,i)` and `(g,j)`.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem signedBasis_inner_hasLocalDegree_two
    (g : Fin s) (i j : Fin n) :
    HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) 2
      (fun z : RawSample s b n =>
        ⟪signedBasis (toSample z) g i, signedBasis (toSample z) g j⟫_ℝ) := by
  apply HasLocalDegree.atom {(g, i), (g, j)} _
  · simpa using
      (Finset.card_insert_le (g, i) ({(g, j)} : Finset (Fin s × Fin n)))
  · intro z z' hagree
    have hi : z (g, i) = z' (g, i) := by
      exact hagree (g, i) (by simp)
    have hj : z (g, j) = z' (g, j) := by
      exact hagree (g, j) (by simp)
    change
      ⟪signedBasis (toSample z) g i, signedBasis (toSample z) g j⟫_ℝ =
        ⟪signedBasis (toSample z') g i, signedBasis (toSample z') g j⟫_ℝ
    rw [inner_signedBasis, inner_signedBasis]
    simp only [toSample_hash, toSample_sign]
    have hiHash := congrArg (fun x : SignedHash b => x.1) hi
    have hjHash := congrArg (fun x : SignedHash b => x.1) hj
    have hiSign := congrArg (fun x : SignedHash b => x.2) hi
    have hjSign := congrArg (fun x : SignedHash b => x.2) hj
    simp only [hiHash, hjHash, hiSign, hjSign]
    rfl

/-- Every scalar entry of the pointwise SparseStack Gram error has local
interaction degree at most two.  The proof uses the exact hollow identity,
so no independence is involved.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_entry_hasLocalDegree_two
    (hs : 0 < s) (F : Frame n d) (a c : Fin d) :
    HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) 2
      (fun z : RawSample s b n => (gramError F (toSample z)) a c) := by
  have hinner (g : Fin s) (i j : Fin n) :
      HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) 2
        (fun z : RawSample s b n =>
          ⟪signedBasis (toSample z) g i,
            signedBasis (toSample z) g j⟫_ℝ * F.u i a * F.u j c) := by
    have h := signedBasis_inner_hasLocalDegree_two
      (b := b) g i j
    have hscaled := HasLocalDegree.smul (F.u i a * F.u j c) h
    convert hscaled using 1
    funext z
    ring
  have hsum :
      HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) 2
        (fun z : RawSample s b n =>
          ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
            ⟪signedBasis (toSample z) g i,
              signedBasis (toSample z) g j⟫_ℝ * F.u i a * F.u j c) := by
    apply HasLocalDegree.sum_fintype
    intro g
    apply HasLocalDegree.sum_fintype
    intro i
    apply HasLocalDegree.sum_finset (Finset.univ.erase i)
      (fun j z =>
        ⟪signedBasis (toSample z) g i,
          signedBasis (toSample z) g j⟫_ℝ * F.u i a * F.u j c)
    intro j hj
    exact hinner g i j
  have hscaled := HasLocalDegree.smul (1 / (s : ℝ)) hsum
  apply HasLocalDegree.congr hscaled
  funext z
  have hblock := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A a c)
    (gramError_eq_block_first F (toSample z) hs)
  simpa using hblock.symm

/-- An entry of the `r`-th Gram-error power has interaction degree at most
`2r`.  This recursive noncommutative expansion is the formal word count.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_pow_entry_hasLocalDegree
    (hs : 0 < s) (F : Frame n d) (r : ℕ) (a c : Fin d) :
    HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) (2 * r)
      (fun z : RawSample s b n => ((gramError F (toSample z)) ^ r) a c) := by
  induction r generalizing a c with
  | zero =>
      simpa using
        (HasLocalDegree.constant (ι := Fin s × Fin n)
          (α := SignedHash b) 0 ((1 : Matrix (Fin d) (Fin d) ℝ) a c))
  | succ r ihr =>
      have hsum :
          HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b)
            (2 * r + 2)
            (fun z : RawSample s b n =>
              ∑ x : Fin d,
                ((gramError F (toSample z)) ^ r) a x *
                  (gramError F (toSample z)) x c) := by
        apply HasLocalDegree.sum_fintype
        intro x
        exact HasLocalDegree.mul (ihr a x)
          (gramError_entry_hasLocalDegree_two (b := b) hs F x c)
      have hdegree :
          HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b)
            (2 * (Nat.succ r))
            (fun z : RawSample s b n =>
              ∑ x : Fin d,
                ((gramError F (toSample z)) ^ r) a x *
                  (gramError F (toSample z)) x c) := by
        simpa [Nat.mul_succ] using hsum
      apply HasLocalDegree.congr hdegree
      funext z
      rw [pow_succ, Matrix.mul_apply]

/-- The `r`-th trace-power observable also has local degree at most `2r`.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_power_hasLocalDegree
    (hs : 0 < s) (F : Frame n d) (r : ℕ) :
    HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) (2 * r)
      (fun z : RawSample s b n =>
        ((gramError F (toSample z)) ^ r).trace) := by
  have hsum :
      HasLocalDegree (ι := Fin s × Fin n) (α := SignedHash b) (2 * r)
        (fun z : RawSample s b n =>
          ∑ a : Fin d, ((gramError F (toSample z)) ^ r) a a) := by
    apply HasLocalDegree.sum_fintype
    intro a
    exact gramError_pow_entry_hasLocalDegree (b := b) hs F r a a
  apply HasLocalDegree.congr hsum
  funext z
  rfl

/-- **Exact `4q`-wise trace-moment transfer.**  If an arbitrary finite law on
combined signed-hash selectors has the same marginals through order `4q` as
the fully independent law, then its `2q` trace moment is identical to the
fully independent trace moment.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_even_moment_eq_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d) (q : ℕ)
    (μ : FiniteLaw (RawSample s b n))
    (hmatch : MatchesUpTo μ (rawSampleLaw s b n hb) (4 * q)) :
    μ.expect (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) =
      (rawSampleLaw s b n hb).expect
        (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) := by
  apply HasLocalDegree.expect_eq_of_matchesUpTo hmatch
  have hdegree : 2 * (2 * q) = 4 * q := by omega
  simpa only [hdegree] using
    (trace_power_hasLocalDegree (b := b) hs F (2 * q))

/-- Matrix Markov for a `4q`-wise matching law, with the right side replaced
exactly by the corresponding fully independent trace moment.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_markov_tail_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d)
    (q : ℕ) (hq : 0 < q) (eps : ℝ) (heps : 0 < eps)
    (μ : FiniteLaw (RawSample s b n))
    (hmatch : MatchesUpTo μ (rawSampleLaw s b n hb) (4 * q)) :
    μ.prob {z | eps ≤ ‖gramError F (toSample z)‖} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  have htail := MatrixTail.matrix_markov_tail μ
    (fun z => gramError F (toSample z))
    (fun z => MatrixTail.sparseStack_gramError_isHermitian F (toSample z))
    q hq eps heps
  rw [trace_even_moment_eq_of_matchesUpTo_four_mul hs hb F q μ hmatch] at htail
  exact htail

/-- OSE-failure form of the limited-independence Markov endpoint.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ose_failure_tail_of_matchesUpTo_four_mul
    (hs : 0 < s) (hb : 0 < b) (F : Frame n d)
    (q : ℕ) (hq : 0 < q) (eps : ℝ) (heps : 0 < eps)
    (μ : FiniteLaw (RawSample s b n))
    (hmatch : MatchesUpTo μ (rawSampleLaw s b n hb) (4 * q)) :
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        eps ^ (2 * q) := by
  calc
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤
        μ.prob {z | eps ≤ ‖gramError F (toSample z)‖} := by
      apply FiniteLaw.prob_mono
      intro z hfail
      have hiff := MatrixTail.sparseStack_gramError_norm_le_iff_vector_ose
        F (toSample z) eps heps.le
      by_contra htail
      exact hfail (hiff.mp (not_le.mp htail).le)
    _ ≤ (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        eps ^ (2 * q) :=
      matrix_markov_tail_of_matchesUpTo_four_mul
        hs hb F q hq eps heps μ hmatch

/-- The concrete sparse-Fock moment estimate therefore applies unchanged to
any `4q`-wise matching law.  This is the reusable limited-independence
endpoint before the report's separate generator/seed instantiation.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem failure_tail_of_band_bounds
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d)
    {q : ℕ} (hq : 0 < q) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta)
    {eps : ℝ} (heps : 0 < eps)
    (μ : FiniteLaw (RawSample s b n))
    (hmatch : MatchesUpTo μ
      (rawSampleLaw s b n (lt_trans Nat.zero_lt_one hb)) (4 * q)) :
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤
      (d : ℝ) * ((3 * cB b ^ 2 * beta) / eps) ^ (2 * q) := by
  have hmarkov := ose_failure_tail_of_matchesUpTo_four_mul
    hs (lt_trans Nat.zero_lt_one hb) F q hq eps heps μ hmatch
  have hmoment := raw_trace_moment_le_of_band_bounds
    hs hb F hbeta hband
  calc
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤
        (rawSampleLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
            (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
          eps ^ (2 * q) := hmarkov
    _ ≤ ((d : ℝ) * (3 * cB b ^ 2 * beta) ^ (2 * q)) /
          eps ^ (2 * q) := by
      exact div_le_div_of_nonneg_right hmoment (pow_nonneg heps.le _)
    _ = (d : ℝ) * ((3 * cB b ^ 2 * beta) / eps) ^ (2 * q) := by
      rw [div_pow]
      ring

/-- **Canonical limited-independence SparseStack theorem.**  At the exact
rounded parameters of the fully independent theorem, `4q`-coordinate
marginal agreement (where `q = failureOrder d delta`) gives the same failure
probability `≤ delta`.  All constants and the band estimate are imported from
the already proved fully independent sparse-Fock argument.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_ose_failure_le_delta
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (μ : FiniteLaw
      (RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n))
    (hmatch : MatchesUpTo μ
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1))
      (4 * failureOrder d delta)) :
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤ delta := by
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
      (rawSampleLaw s b n (lt_trans Nat.zero_lt_one hb)) (4 * q) := by
    simpa [q, s, b] using hmatch
  have htail := failure_tail_of_band_bounds
    hs hb F hq hbeta0 hband heps0 μ hmatch'
  have hcB0 : 0 ≤ cB b :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (SparseIIDCoupling.one_le_cB (lt_trans Nat.zero_lt_one hb))
  have hcBStar : cB b ≤ cStar :=
    SparseIIDCoupling.cB_le_cStar (lt_trans Nat.zero_lt_one hb)
  have hcSq : cB b ^ 2 ≤ cStar ^ 2 := by
    nlinarith [PaperParameters.cStar_pos]
  have hbase0 : 0 ≤ 3 * cB b ^ 2 * beta / eps := by positivity
  have hbase : 3 * cB b ^ 2 * beta / eps ≤
      roundedMomentBase d q eps := by
    rw [roundedMomentBase]
    apply div_le_div_of_nonneg_right _ heps0.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcSq (by norm_num)) hbeta0
  have hpow : (3 * cB b ^ 2 * beta / eps) ^ (2 * q) ≤
      (roundedMomentBase d q eps) ^ (2 * q) :=
    pow_le_pow_left₀ hbase0 hbase _
  calc
    μ.prob {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} ≤
        (d : ℝ) * (3 * cB b ^ 2 * beta / eps) ^ (2 * q) := by
      simpa [q, s, b, beta] using htail
    _ ≤ (d : ℝ) * (roundedMomentBase d q eps) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ delta := by
      simpa [q] using rounded_scalar_failure_le_delta
        hd hdelta0 hdelta1 heps0 heps1

/-- Equivalent operator-norm statement of the canonical endpoint.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_operator_norm_failure_le_delta
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (μ : FiniteLaw
      (RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n))
    (hmatch : MatchesUpTo μ
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1))
      (4 * failureOrder d delta)) :
    μ.prob {z | eps < ‖gramError F (toSample z)‖} ≤ delta := by
  have hevent :
      {z : RawSample (roundedS (failureOrder d delta) eps)
          (roundedB d (failureOrder d delta) eps) n |
        eps < ‖gramError F (toSample z)‖} =
      {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} := by
    ext z
    have hiff := MatrixTail.sparseStack_gramError_norm_le_iff_vector_ose
      F (toSample z) eps heps0.le
    simpa [not_le] using not_congr hiff
  rw [hevent]
  exact rounded_ose_failure_le_delta
    hd hdelta0 hdelta1 heps0 heps1 F μ hmatch

/-- Success-probability form of the canonical limited-independence theorem.

Source: ported from `SparseFockFormal.SparseStackLimitedIndependence`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_ose_success_probability
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (μ : FiniteLaw
      (RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n))
    (hmatch : MatchesUpTo μ
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1))
      (4 * failureOrder d delta)) :
    1 - delta ≤
      μ.prob {z | MatrixTail.IsSparseStackOSE F (toSample z) eps} := by
  let good : Set
      (RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n) :=
    {z | MatrixTail.IsSparseStackOSE F (toSample z) eps}
  have hfail : μ.prob goodᶜ ≤ delta := by
    have hcomp : goodᶜ =
        {z | ¬ MatrixTail.IsSparseStackOSE F (toSample z) eps} := by
      ext z
      rfl
    rw [hcomp]
    exact rounded_ose_failure_le_delta
      hd hdelta0 hdelta1 heps0 heps1 F μ hmatch
  calc
    1 - delta ≤ 1 - μ.prob goodᶜ := sub_le_sub_left hfail 1
    _ = μ.prob good := by
      simpa using (FiniteLaw.prob_compl μ goodᶜ).symm
    _ = μ.prob {z | MatrixTail.IsSparseStackOSE F (toSample z) eps} := rfl

end

end SparseStackLimitedIndependence

end NLAlib.SparseFock

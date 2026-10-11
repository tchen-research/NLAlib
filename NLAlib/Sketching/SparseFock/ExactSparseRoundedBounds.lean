/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactSparseProjectionTail

set_option autoImplicit false

/-!
# Exact-s rounded parameter bounds

The exact constants convert band bounds into rounded operator and OSE probabilities.
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

/-- All scalar arithmetic is discharged once the rounded band envelope is
available.  The sharp inequality `exactScale ≤ cB ≤ cStar` gives exactly the
same final scalar bound as in the SparseStack theorem.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_rounded_failure_le_delta_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) F
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | ¬ IsUniformExactSOSE F X eps} ≤ delta := by
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
  have hband' : ∀ shift nu, nu ≤ 2 * q →
      ‖normalizedBand (s * b) F b shift *
        gradeProjection (d := d) nu‖ ≤ beta := by
    intro shift nu hnu
    dsimp [q, s, b, beta]
    exact hband shift nu hnu
  have htail := uniformExactS_failure_tail_of_band_bounds
    (n := n) (s := s) (b := b) hs hb F hq hbeta0 hband' heps0
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
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | ¬ IsUniformExactSOSE F X eps} =
        (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb0)).prob
          {X | ¬ IsUniformExactSOSE F X eps} := by
      simp [s, b, q]
    _ ≤ (d : ℝ) * (3 * scale ^ 2 * beta / eps) ^ (2 * q) := htail
    _ ≤ (d : ℝ) * (roundedMomentBase d q eps) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ delta := by
      simpa [q] using rounded_scalar_failure_le_delta
        hd hdelta0 hdelta1 heps0 heps1

/-- Canonical operator-norm tail, conditional only on the displayed band
envelope.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_rounded_operator_norm_failure_le_delta_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) F
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps < ‖gramError F X‖} ≤ delta := by
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
  exact uniformExactS_rounded_failure_le_delta_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 F hband

/-- Canonical OSE success probability, conditional only on the displayed band
envelope.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_rounded_success_probability_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) F
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    1 - delta ≤
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsUniformExactSOSE F X eps} := by
  let mu := exactSampleLaw (n := n)
    (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
      (MainTheoremAssembly.canonicalB_pos
        (d := d) (delta := delta) heps0 heps1))
  let good : Set (ExactSample
      (roundedS (failureOrder d delta) eps *
        roundedB d (failureOrder d delta) eps)
      (roundedS (failureOrder d delta) eps) n) :=
    {X | IsUniformExactSOSE F X eps}
  have hfail : mu.prob goodᶜ ≤ delta := by
    change mu.prob {X | ¬ IsUniformExactSOSE F X eps} ≤ delta
    exact uniformExactS_rounded_failure_le_delta_of_band_bounds
      hd hdelta0 hdelta1 heps0 heps1 F hband
  calc
    1 - delta ≤ 1 - mu.prob goodᶜ := sub_le_sub_left hfail 1
    _ = mu.prob good := by
      simpa using (FiniteLaw.prob_compl mu goodᶜ).symm
    _ = _ := rfl

/-- Hypothesis-free canonical operator-norm tail.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_rounded_operator_norm_failure_le_delta
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps < ‖gramError F X‖} ≤ delta := by
  apply uniformExactS_rounded_operator_norm_failure_le_delta_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 F
  intro shift nu hnu
  exact MainTheorem.rounded_band_bound heps0 heps1 F shift nu hnu

/-- Hypothesis-free canonical exact-`s` OSE success probability.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_rounded_ose_success
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    1 - delta ≤
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsUniformExactSOSE F X eps} := by
  apply uniformExactS_rounded_success_probability_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 F
  intro shift nu hnu
  exact MainTheorem.rounded_band_bound heps0 heps1 F shift nu hnu

end

end NLAlib.SparseFock.UniformExactS

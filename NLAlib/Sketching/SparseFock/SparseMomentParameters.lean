/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseRoundedScales

set_option autoImplicit false

/-!
# Sparse moment parameter estimates

The rounded band envelope, moment base, failure probability, and final parameter package.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace PaperParameters

/-- Scalar parameter substitution behind lines 1437--1446.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem betaEnvelope_le_three_Cband
    {d q : ℕ} {m s epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hm : 0 < m) (hs : 0 < s)
    (hmScale : L ^ 2 * (Dq d q : ℝ) ≤ epsilon ^ 2 * m)
    (hsScale : L * ((2 * q + 1 : ℕ) : ℝ) ≤ epsilon * s) :
    betaEnvelope d q m s ≤ 3 * Cband * epsilon / L := by
  have hL1 : (1 : ℝ) ≤ L := by nlinarith [ninety_lt_L]
  have hepsilonL : epsilon ≤ L := hepsilon1.trans hL1
  have hdense : (Dq d q : ℝ) / m ≤ epsilon ^ 2 / L ^ 2 := by
    apply (div_le_div_iff₀ hm (sq_pos_of_pos L_pos)).2
    nlinarith
  have ht0 : 0 ≤ epsilon / L := (div_pos hepsilon0 L_pos).le
  have ht1 : epsilon / L ≤ 1 := (div_le_one L_pos).2 hepsilonL
  have hlinear : (Dq d q : ℝ) / m ≤ epsilon / L := by
    calc
      (Dq d q : ℝ) / m ≤ epsilon ^ 2 / L ^ 2 := hdense
      _ = (epsilon / L) ^ 2 := by field_simp
      _ ≤ epsilon / L := by nlinarith [sq_nonneg (epsilon / L)]
  have hroot : Real.sqrt ((Dq d q : ℝ) / m) ≤ epsilon / L := by
    rw [Real.sqrt_le_iff]
    exact ⟨ht0, by simpa [div_pow] using hdense⟩
  have hsparse : ((2 * q + 1 : ℕ) : ℝ) / s ≤ epsilon / L := by
    apply (div_le_div_iff₀ hs L_pos).2
    nlinarith
  rw [betaEnvelope]
  have hsum : Real.sqrt ((Dq d q : ℝ) / m) +
      (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s ≤
        3 * (epsilon / L) := by linarith
  calc
    Cband * (Real.sqrt ((Dq d q : ℝ) / m) +
        (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s) ≤
        Cband * (3 * (epsilon / L)) :=
      mul_le_mul_of_nonneg_left hsum Cband_pos.le
    _ = 3 * Cband * epsilon / L := by ring

/-- The rounded parameters satisfy the exact beta-envelope substitution.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_betaEnvelope_le
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) ≤
      3 * Cband * epsilon / L := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon0
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hmLower := roundedM_lower (d := d) (q := q) hepsilon0
  have hm : (0 : ℝ) < roundedM d q epsilon :=
    (M0_pos hepsilon0).trans_le hmLower
  have hmScale : L ^ 2 * (Dq d q : ℝ) ≤
      epsilon ^ 2 * (roundedM d q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ (sq_pos_of_pos hepsilon0)).mp
      (by simpa [M0] using hmLower)
    simpa [mul_comm] using hraw
  have hsScale : L * ((2 * q + 1 : ℕ) : ℝ) ≤
      epsilon * (roundedS q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ hepsilon0).mp
      (roundedS_lower q epsilon)
    simpa [mul_comm] using hraw
  exact betaEnvelope_le_three_Cband hepsilon0 hepsilon1 hm hs hmScale hsScale

/-- After convex-order scaling, the rounded envelope has base below
`(3 + sqrt 2)/10`, hence below `0.442` and `1/2`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_moment_base_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * cStar ^ 2 *
        betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon <
      (221 : ℝ) / 500 := by
  have hbeta := rounded_betaEnvelope_le (d := d) (q := q) hepsilon0 hepsilon1
  have hscaled :
      3 * cStar ^ 2 *
          betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon ≤
        Cband / 10 := by
    calc
      3 * cStar ^ 2 *
          betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon ≤
          3 * cStar ^ 2 * (3 * Cband * epsilon / L) / epsilon := by
        apply (div_le_div_iff_of_pos_right hepsilon0).2
        exact mul_le_mul_of_nonneg_left hbeta (by positivity)
      _ = Cband / 10 := by
        rw [L]
        field_simp [ne_of_gt cStar_pos, ne_of_gt hepsilon0]
        ring
  exact hscaled.trans_lt Cband_div_ten_lt_442

/-- The rounded moment-base estimate is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_moment_base_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * cStar ^ 2 *
        betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon <
      (1 : ℝ) / 2 :=
  (rounded_moment_base_lt_442 hepsilon0 hepsilon1).trans (by norm_num)

/-- The defined rounded moment base is strictly below 221/500.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedMomentBase_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    roundedMomentBase d q epsilon < (221 : ℝ) / 500 := by
  simpa [roundedMomentBase] using
    rounded_moment_base_lt_442 (d := d) (q := q) hepsilon0 hepsilon1

/-- The defined rounded moment base is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedMomentBase_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    roundedMomentBase d q epsilon < (1 : ℝ) / 2 := by
  simpa [roundedMomentBase] using
    rounded_moment_base_lt_half (d := d) (q := q) hepsilon0 hepsilon1

/-- The defined rounded moment base is nonnegative.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedMomentBase_nonneg
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ≤ roundedMomentBase d q epsilon := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hmLower := roundedM_lower (d := d) (q := q) hepsilon
  have hm : (0 : ℝ) < roundedM d q epsilon :=
    (M0_pos hepsilon).trans_le hmLower
  have hDq : (0 : ℝ) ≤ (Dq d q : ℕ) := by positivity
  have hcount : (0 : ℝ) ≤ ((2 * q + 1 : ℕ) : ℕ) := by positivity
  have hbeta : 0 ≤ betaEnvelope d q (roundedM d q epsilon)
      (roundedS q epsilon) := by
    rw [betaEnvelope]
    exact mul_nonneg Cband_pos.le <| add_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hDq hm.le))
      (div_nonneg hcount hs.le)
  rw [roundedMomentBase]
  exact div_nonneg (mul_nonneg (by positivity) hbeta) hepsilon.le

/-- The complete scalar failure arithmetic for the rounded v1.4 parameters.
The remaining probabilistic task is to prove that the actual failure
probability is bounded by this scalar expression.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_scalar_failure_le_delta
    {d : ℕ} {delta epsilon : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (d : ℝ) *
        (roundedMomentBase d (failureOrder d delta) epsilon) ^
          (2 * failureOrder d delta) ≤ delta := by
  let q := failureOrder d delta
  let rho := roundedMomentBase d q epsilon
  have hrho0 : 0 ≤ rho := by
    simpa [rho, q] using
      roundedMomentBase_nonneg (d := d) (q := failureOrder d delta) hepsilon0
  have hrho : rho ≤ (1 : ℝ) / 2 := by
    exact (roundedMomentBase_lt_half (d := d) (q := q) hepsilon0 hepsilon1).le
  have hpow : rho ^ (2 * q) ≤ ((1 : ℝ) / 2) ^ (2 * q) :=
    pow_le_pow_left₀ hrho0 hrho _
  have hhalfFour : ((1 : ℝ) / 2) ^ (2 * q) = ((1 : ℝ) / 4) ^ q := by
    rw [pow_mul]
    norm_num
  calc
    (d : ℝ) *
        (roundedMomentBase d (failureOrder d delta) epsilon) ^
          (2 * failureOrder d delta) = (d : ℝ) * rho ^ (2 * q) := by
      simp [rho, q]
    _ ≤ (d : ℝ) * (((1 : ℝ) / 2) ^ (2 * q)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (d : ℝ) * ((1 : ℝ) / 4) ^ q := by rw [hhalfFour]
    _ ≤ delta := by
      simpa [q] using four_pow_failureOrder_le hd hdelta0 hdelta1

/-- Canonical scale conditions and explicit dimensions, specialized to the
base-two failure order selected by the paper.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem main_parameter_package
    {d : ℕ} {delta epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    L * ((2 * failureOrder d delta + 1 : ℕ) : ℝ) / epsilon ≤
        (roundedS (failureOrder d delta) epsilon : ℝ) ∧
    M0 d (failureOrder d delta) epsilon ≤
        (roundedM d (failureOrder d delta) epsilon : ℝ) ∧
    (roundedS (failureOrder d delta) epsilon : ℝ) <
        1356 * (failureOrder d delta : ℝ) / epsilon ∧
    (roundedM d (failureOrder d delta) epsilon : ℝ) <
        306456 * ((d : ℝ) + failureOrder d delta) / epsilon ^ 2 ∧
    2 ≤ roundedB d (failureOrder d delta) epsilon := by
  let q := failureOrder d delta
  have hq : 1 ≤ q := one_le_failureOrder d delta
  exact ⟨roundedS_lower q epsilon,
    roundedM_lower hepsilon0,
    roundedS_lt_1356 hq hepsilon0 hepsilon1,
    roundedM_lt_306456 hd hq hepsilon0 hepsilon1,
    two_le_roundedB hq hepsilon0 hepsilon1⟩

end PaperParameters

end NLAlib.SparseFock

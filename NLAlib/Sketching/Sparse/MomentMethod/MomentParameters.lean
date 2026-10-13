/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.MomentMethod.RoundedScales

/-!
# Sparse moment parameter estimates

The rounded band envelope, moment base, failure probability, and final parameter package.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- Scalar parameter substitution behind lines 1437--1446.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem bandEnvelope_le_three_bandConstant
    {d q : ℕ} {m s epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hm : 0 < m) (hs : 0 < s)
    (hmScale : scaleConstant ^ 2 * (momentDim d q : ℝ) ≤ epsilon ^ 2 * m)
    (hsScale : scaleConstant * ((2 * q + 1 : ℕ) : ℝ) ≤ epsilon * s) :
    bandEnvelope d q m s ≤ 3 * bandConstant * epsilon / scaleConstant := by
  have hL1 : (1 : ℝ) ≤ scaleConstant := by nlinarith [ninety_lt_scaleConstant]
  have hepsilonL : epsilon ≤ scaleConstant := hepsilon1.trans hL1
  have hdense : (momentDim d q : ℝ) / m ≤ epsilon ^ 2 / scaleConstant ^ 2 := by
    apply (div_le_div_iff₀ hm (sq_pos_of_pos scaleConstant_pos)).2
    nlinarith
  have ht0 : 0 ≤ epsilon / scaleConstant := (div_pos hepsilon0 scaleConstant_pos).le
  have ht1 : epsilon / scaleConstant ≤ 1 := (div_le_one scaleConstant_pos).2 hepsilonL
  have hlinear : (momentDim d q : ℝ) / m ≤ epsilon / scaleConstant := by
    calc
      (momentDim d q : ℝ) / m ≤ epsilon ^ 2 / scaleConstant ^ 2 := hdense
      _ = (epsilon / scaleConstant) ^ 2 := by field_simp
      _ ≤ epsilon / scaleConstant := by nlinarith [sq_nonneg (epsilon / scaleConstant)]
  have hroot : Real.sqrt ((momentDim d q : ℝ) / m) ≤ epsilon / scaleConstant := by
    rw [Real.sqrt_le_iff]
    exact ⟨ht0, by simpa [div_pow] using hdense⟩
  have hsparse : ((2 * q + 1 : ℕ) : ℝ) / s ≤ epsilon / scaleConstant := by
    apply (div_le_div_iff₀ hs scaleConstant_pos).2
    nlinarith
  rw [bandEnvelope]
  have hsum : Real.sqrt ((momentDim d q : ℝ) / m) +
      (momentDim d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s ≤
        3 * (epsilon / scaleConstant) := by linarith
  calc
    bandConstant * (Real.sqrt ((momentDim d q : ℝ) / m) +
        (momentDim d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s) ≤
        bandConstant * (3 * (epsilon / scaleConstant)) :=
      mul_le_mul_of_nonneg_left hsum bandConstant_pos.le
    _ = 3 * bandConstant * epsilon / scaleConstant := by ring

/-- The rounded parameters satisfy the exact beta-envelope substitution.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_bandEnvelope_le
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) ≤
      3 * bandConstant * epsilon / scaleConstant := by
  have hsNat : 0 < sparseColumnSparsity q epsilon := sparseColumnSparsity_pos hepsilon0
  have hs : (0 : ℝ) < sparseColumnSparsity q epsilon := by exact_mod_cast hsNat
  have hmLower := sparseRows_lower (d := d) (q := q) hepsilon0
  have hm : (0 : ℝ) < sparseRows d q epsilon :=
    (rowTarget_pos hepsilon0).trans_le hmLower
  have hmScale : scaleConstant ^ 2 * (momentDim d q : ℝ) ≤
      epsilon ^ 2 * (sparseRows d q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ (sq_pos_of_pos hepsilon0)).mp
      (by simpa [rowTarget] using hmLower)
    simpa [mul_comm] using hraw
  have hsScale : scaleConstant * ((2 * q + 1 : ℕ) : ℝ) ≤
      epsilon * (sparseColumnSparsity q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ hepsilon0).mp
      (sparseColumnSparsity_lower q epsilon)
    simpa [mul_comm] using hraw
  exact bandEnvelope_le_three_bandConstant hepsilon0 hepsilon1 hm hs hmScale hsScale

/-- After convex-order scaling, the rounded envelope has base below
`(3 + sqrt 2)/10`, hence below `0.442` and `1/2`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_moment_base_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * convexOrderConstant ^ 2 *
        bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) / epsilon <
      (221 : ℝ) / 500 := by
  have hbeta := rounded_bandEnvelope_le (d := d) (q := q) hepsilon0 hepsilon1
  have hscaled :
      3 * convexOrderConstant ^ 2 *
          bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) / epsilon ≤
        bandConstant / 10 := by
    calc
      3 * convexOrderConstant ^ 2 *
          bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) / epsilon ≤
          3 * convexOrderConstant ^ 2 * (3 * bandConstant * epsilon / scaleConstant) / epsilon := by
        apply (div_le_div_iff_of_pos_right hepsilon0).2
        exact mul_le_mul_of_nonneg_left hbeta (by positivity)
      _ = bandConstant / 10 := by
        rw [scaleConstant]
        field_simp [ne_of_gt convexOrderConstant_pos, ne_of_gt hepsilon0]
        ring
  exact hscaled.trans_lt bandConstant_div_ten_lt_442

/-- The rounded moment-base estimate is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rounded_moment_base_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * convexOrderConstant ^ 2 *
        bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) / epsilon <
      (1 : ℝ) / 2 :=
  (rounded_moment_base_lt_442 hepsilon0 hepsilon1).trans (by norm_num)

/-- The defined rounded moment base is strictly below 221/500.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem momentBase_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    momentBase d q epsilon < (221 : ℝ) / 500 := by
  simpa [momentBase] using
    rounded_moment_base_lt_442 (d := d) (q := q) hepsilon0 hepsilon1

/-- The defined rounded moment base is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem momentBase_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    momentBase d q epsilon < (1 : ℝ) / 2 := by
  simpa [momentBase] using
    rounded_moment_base_lt_half (d := d) (q := q) hepsilon0 hepsilon1

/-- The defined rounded moment base is nonnegative.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem momentBase_nonneg
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ≤ momentBase d q epsilon := by
  have hsNat : 0 < sparseColumnSparsity q epsilon := sparseColumnSparsity_pos hepsilon
  have hs : (0 : ℝ) < sparseColumnSparsity q epsilon := by exact_mod_cast hsNat
  have hmLower := sparseRows_lower (d := d) (q := q) hepsilon
  have hm : (0 : ℝ) < sparseRows d q epsilon :=
    (rowTarget_pos hepsilon).trans_le hmLower
  have hDq : (0 : ℝ) ≤ (momentDim d q : ℕ) := by positivity
  have hcount : (0 : ℝ) ≤ ((2 * q + 1 : ℕ) : ℕ) := by positivity
  have hbeta : 0 ≤ bandEnvelope d q (sparseRows d q epsilon)
      (sparseColumnSparsity q epsilon) := by
    rw [bandEnvelope]
    exact mul_nonneg bandConstant_pos.le <| add_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hDq hm.le))
      (div_nonneg hcount hs.le)
  rw [momentBase]
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
        (momentBase d (sparseMomentOrder d delta) epsilon) ^
          (2 * sparseMomentOrder d delta) ≤ delta := by
  let q := sparseMomentOrder d delta
  let rho := momentBase d q epsilon
  have hrho0 : 0 ≤ rho := by
    simpa [rho, q] using
      momentBase_nonneg (d := d) (q := sparseMomentOrder d delta) hepsilon0
  have hrho : rho ≤ (1 : ℝ) / 2 := by
    exact (momentBase_lt_half (d := d) (q := q) hepsilon0 hepsilon1).le
  have hpow : rho ^ (2 * q) ≤ ((1 : ℝ) / 2) ^ (2 * q) :=
    pow_le_pow_left₀ hrho0 hrho _
  have hhalfFour : ((1 : ℝ) / 2) ^ (2 * q) = ((1 : ℝ) / 4) ^ q := by
    rw [pow_mul]
    norm_num
  calc
    (d : ℝ) *
        (momentBase d (sparseMomentOrder d delta) epsilon) ^
          (2 * sparseMomentOrder d delta) = (d : ℝ) * rho ^ (2 * q) := by
      simp [rho, q]
    _ ≤ (d : ℝ) * (((1 : ℝ) / 2) ^ (2 * q)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (d : ℝ) * ((1 : ℝ) / 4) ^ q := by rw [hhalfFour]
    _ ≤ delta := by
      simpa [q] using four_pow_sparseMomentOrder_le hd hdelta0 hdelta1

/-- Canonical scale conditions and explicit dimensions, specialized to the
base-two failure order selected by the paper.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem main_parameter_package
    {d : ℕ} {delta epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    scaleConstant * ((2 * sparseMomentOrder d delta + 1 : ℕ) : ℝ) / epsilon ≤
        (sparseColumnSparsity (sparseMomentOrder d delta) epsilon : ℝ) ∧
    rowTarget d (sparseMomentOrder d delta) epsilon ≤
        (sparseRows d (sparseMomentOrder d delta) epsilon : ℝ) ∧
    (sparseColumnSparsity (sparseMomentOrder d delta) epsilon : ℝ) <
        1356 * (sparseMomentOrder d delta : ℝ) / epsilon ∧
    (sparseRows d (sparseMomentOrder d delta) epsilon : ℝ) <
        306456 * ((d : ℝ) + sparseMomentOrder d delta) / epsilon ^ 2 ∧
    2 ≤ sparseBlockRows d (sparseMomentOrder d delta) epsilon := by
  let q := sparseMomentOrder d delta
  have hq : 1 ≤ q := one_le_sparseMomentOrder d delta
  exact ⟨sparseColumnSparsity_lower q epsilon,
    sparseRows_lower hepsilon0,
    sparseColumnSparsity_lt_1356 hq hepsilon0 hepsilon1,
    sparseRows_lt_306456 hd hq hepsilon0 hepsilon1,
    two_le_sparseBlockRows hq hepsilon0 hepsilon1⟩

end NLAlib.SparseSketch

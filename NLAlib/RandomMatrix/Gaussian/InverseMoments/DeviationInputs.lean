/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.RandomMatrix.Gaussian.InverseMoments.FrobeniusMoments
import NLAlib.RandomMatrix.Gaussian.InverseMoments.SpectralTail

/-!
# Gaussian inverse tails at the randomized SVD thresholds

The native inverse-chi-square moment argument sharpens the Frobenius failure constant to one.
The positive-head spectral tail includes a one-row head. Together they give two bad head
events of probability at most `t⁻ᵖ`, including the empty head.
Source: HMT (2011), proofs of Theorems 10.7–10.8, with the improved native Frobenius estimate;
supports atlas `rsvd-tail`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The Frobenius inverse bad event has coefficient one at the frozen RSVD threshold.
Source: the sharpened native inverse-chi-square moment proof; supports atlas `rsvd-tail`. -/
theorem gaussianMatrix_lt_frobNorm_pinvR_le_sharp {r p : ℕ} (hp : 4 ≤ p)
    (t : ℝ) (ht : 1 ≤ t) :
    (gaussianMatrix (Fin r) (Fin (r + p))).real
      {G | t * Real.sqrt (12 * (r : ℝ) / p) < frobNorm (pinvR G)} ≤ t ^ (-(p : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := gaussianMatrix_lt_frobSq_pinvR_le_sharp (r := r) (k := r + p)
    (by omega) (t ^ 2) (by nlinarith)
  have hgap : ((r + p : ℕ) : ℝ) - r = p := by push_cast; ring
  rw [hgap] at h
  have he : {G : Matrix (Fin r) (Fin (r + p)) ℝ |
      t * Real.sqrt (12 * (r : ℝ) / p) < frobNorm (pinvR G)} =
      {G | 12 * (r : ℝ) / p * t ^ 2 < frobSq (pinvR G)} := by
    ext G
    change t * Real.sqrt (12 * (r : ℝ) / p) < frobNorm (pinvR G) ↔
      12 * (r : ℝ) / p * t ^ 2 < frobSq (pinvR G)
    have hs := Real.sq_sqrt (show 0 ≤ 12 * (r : ℝ) / p by positivity)
    have hn := frobNorm_nonneg (pinvR G)
    have htS := mul_nonneg ht0.le (Real.sqrt_nonneg (12 * (r : ℝ) / p))
    have hF := frobNorm_sq (pinvR G)
    have hth : (t * Real.sqrt (12 * (r : ℝ) / p)) ^ 2 = 12 * (r : ℝ) / p * t ^ 2 := by
      rw [mul_pow, hs]
      ring
    rw [← hF, ← hth]
    exact (sq_lt_sq₀ htS hn).symm
  rw [he]
  convert h using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
  congr 1
  ring

/-- The spectral inverse bad event has coefficient one at `t e sqrt(r+p)/(p+1)`.
The positive-head native tail includes `r=1`; the empty head is identically zero.
Source: HMT (2011), Proposition A.3 and its native positive-head extension; supports `rsvd-tail`. -/
theorem gaussianMatrix_lt_specNorm_pinvR_le_rsvd {r p : ℕ} (hp : 4 ≤ p)
    (t : ℝ) (ht : 1 ≤ t) :
    (gaussianMatrix (Fin r) (Fin (r + p))).real
      {G | t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1)) < specNorm (pinvR G)} ≤
      t ^ (-(p : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    have hz (G : Matrix (Fin 0) (Fin (0 + p)) ℝ) : pinvR G = 0 := Subsingleton.elim _ _
    have he : {G : Matrix (Fin 0) (Fin (0 + p)) ℝ |
        t * (Real.exp 1 * Real.sqrt ((0 : ℝ) + p) / ((p : ℝ) + 1)) < specNorm (pinvR G)} = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, hz, specNorm_zero]
      exact not_lt_of_ge (by positivity)
    simpa only [Nat.cast_zero, he, measureReal_empty] using Real.rpow_nonneg ht0.le (-(p : ℝ))
  let b : ℝ := Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hs := gaussianMatrix_lt_specNorm_pinvR_le_of_pos (r := r) (k := r + p)
    hr (by omega) (t * b) (mul_pos ht0 hb)
  have hgap : ((r + p : ℕ) : ℝ) - r + 1 = (p : ℝ) + 1 := by push_cast; ring
  have hwidth : Real.sqrt ((r + p : ℕ) : ℝ) = Real.sqrt (r + p) := by push_cast; rfl
  rw [hgap, hwidth] at hs
  change _ ≤ (1 / Real.sqrt (2 * Real.pi * ((p : ℝ) + 1))) *
    b ^ ((p : ℝ) + 1) * (t * b) ^ (-((p : ℝ) + 1)) at hs
  have he : b ^ ((p : ℝ) + 1) * (t * b) ^ (-((p : ℝ) + 1)) =
      t ^ (-((p : ℝ) + 1)) := by
    rw [Real.mul_rpow ht0.le hb.le]
    calc
      b ^ ((p : ℝ) + 1) * (t ^ (-((p : ℝ) + 1)) * b ^ (-((p : ℝ) + 1))) =
          t ^ (-((p : ℝ) + 1)) * (b ^ ((p : ℝ) + 1) * b ^ (-((p : ℝ) + 1))) := by ring
      _ = _ := by rw [← Real.rpow_add hb, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [mul_assoc, he] at hs
  have hc : 1 / Real.sqrt (2 * Real.pi * ((p : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  refine hs.trans ?_
  calc
    (1 / Real.sqrt (2 * Real.pi * ((p : ℝ) + 1))) * t ^ (-((p : ℝ) + 1)) ≤
        t ^ (-((p : ℝ) + 1)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
        (Real.rpow_nonneg ht0.le (-((p : ℝ) + 1)))
    _ ≤ t ^ (-(p : ℝ)) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)

end NLAlib

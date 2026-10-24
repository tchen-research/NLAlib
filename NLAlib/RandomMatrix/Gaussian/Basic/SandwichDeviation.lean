/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.RandomMatrix.Gaussian.Basic.LipschitzConcentration
import NLAlib.RandomMatrix.Gaussian.Spectral.Chevet
import NLAlib.RandomMatrix.Gaussian.Moments.SecondMoment
import NLAlib.ForMathlib.MeasureTheory.IntegralSqrt

/-!
# One-sided deviations of Gaussian matrix sandwiches

Fixed left and right factors give a common spectral Lipschitz constant for the Frobenius and
spectral norms. Their native second-moment and Chevet mean estimates therefore imply
one-sided concentration with failure `exp (-u²/2)`, including zero factors.
Source: HMT (2011), Propositions 10.1 and 10.3; supports atlas `rsvd-tail`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- Reverse triangle inequality for the native Frobenius norm. This is a helper for
Gaussian sandwich concentration, supporting atlas `rsvd-tail`. -/
private theorem abs_frobNorm_sub_frobNorm_le {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    (A B : Matrix m n 𝕜) : |frobNorm A - frobNorm B| ≤ frobNorm (A - B) := by
  have h₁ : frobNorm A ≤ frobNorm (A - B) + frobNorm B := by
    simpa only [sub_add_cancel] using frobNorm_add_le (A - B) B
  have h₂ : frobNorm B ≤ frobNorm (A - B) + frobNorm A := by
    have h := frobNorm_add_le (B - A) A
    rw [sub_add_cancel, show B - A = -(A - B) by abel, frobNorm_neg] at h
    exact h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both fixed factors contribute their spectral norms to the Frobenius sandwich Lipschitz
constant. Source: HMT (2011), proof of Theorem 10.7; supports atlas `rsvd-tail`. -/
theorem abs_frobNorm_mul_of_mul_sub_le {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) (X Y : Matrix (Fin p) (Fin m) ℝ) :
    |frobNorm (S * X * T) - frobNorm (S * Y * T)| ≤
      (specNorm S * specNorm T) * frobNorm (X - Y) := by
  refine (abs_frobNorm_sub_frobNorm_le _ _).trans ?_
  rw [show S * X * T - S * Y * T = S * (X - Y) * T by
    rw [Matrix.mul_sub, Matrix.sub_mul]]
  calc
    frobNorm (S * (X - Y) * T) ≤ frobNorm (S * (X - Y)) * specNorm T :=
      frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (specNorm S * frobNorm (X - Y)) * specNorm T :=
      mul_le_mul_of_nonneg_right (frobNorm_mul_le_specNorm_mul_frobNorm _ _)
        (specNorm_nonneg T)
    _ = _ := by ring

/-- The Frobenius mean of a Gaussian sandwich is bounded by the product of the factors'
Frobenius norms. Source: HMT (2011), Proposition 10.1 and Jensen; supports `rsvd-tail`. -/
theorem integral_frobNorm_mul_gaussianMatrix_mul_le {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobNorm (S * G * T) ∂gaussianMatrix (Fin p) (Fin m) ≤ frobNorm S * frobNorm T := by
  have hI := integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm
    (fun G => frobNorm (S * G * T)) (specNorm S * specNorm T)
    (mul_nonneg (specNorm_nonneg S) (specNorm_nonneg T)) (abs_frobNorm_mul_of_mul_sub_le S T)
  have h := integral_le_sqrt_integral_sq hI.1 hI.2
  simp_rw [frobNorm_sq] at h
  rw [integral_frobSq_mul_gaussianMatrix_mul, Real.sqrt_mul (frobSq_nonneg S)] at h
  exact h

private theorem gaussianMatrix_measureReal_gt_le_of_mean_le {p m : ℕ}
    (f : Matrix (Fin p) (Fin m) ℝ → ℝ) {L M u : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hzero : f 0 = 0) (hLip : ∀ X Y, |f X - f Y| ≤ L * frobNorm (X - Y))
    (hmean : ∫ G, f G ∂gaussianMatrix (Fin p) (Fin m) ≤ M) (hu : 0 ≤ u) :
    (gaussianMatrix (Fin p) (Fin m)).real {G | M + u * L < f G} ≤
      Real.exp (-u ^ 2 / 2) := by
  rcases hL.eq_or_lt with hL | hL
  · have hf : ∀ G, f G = 0 := by
      intro G
      have h := hLip G 0
      rw [← hL, zero_mul, hzero, sub_zero] at h
      exact abs_nonpos_iff.mp h
    have he : {G | M + u * L < f G} = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hf G, ← hL, mul_zero, add_zero]
      exact not_lt_of_ge hM
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le
  · have h := (gaussian_concentration f L hL hLip u hu).2
    refine (measureReal_mono ?_).trans h
    intro G hG
    change (∫ Y, f Y ∂gaussianMatrix (Fin p) (Fin m)) + L * u ≤ f G
    change M + u * L < f G at hG
    linarith

/-- A fixed Gaussian sandwich has one-sided Frobenius deviation with the spectral Lipschitz
constant, including zero factors. HMT (2011), proof of Theorem 10.7; supports `rsvd-tail`. -/
theorem gaussianMatrix_lt_frobNorm_mul_mul_le {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (gaussianMatrix (Fin p) (Fin m)).real
      {G | frobNorm S * frobNorm T + u * (specNorm S * specNorm T) <
        frobNorm (S * G * T)} ≤ Real.exp (-u ^ 2 / 2) := by
  exact gaussianMatrix_measureReal_gt_le_of_mean_le _
    (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    (mul_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _))
    (by simp) (abs_frobNorm_mul_of_mul_sub_le S T)
    (integral_frobNorm_mul_gaussianMatrix_mul_le S T) hu

/-- A fixed Gaussian sandwich has one-sided spectral deviation about the Chevet bound,
including zero factors. HMT (2011), proof of Theorem 10.8; supports `rsvd-tail`. -/
theorem gaussianMatrix_lt_specNorm_mul_mul_le {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (gaussianMatrix (Fin p) (Fin m)).real
      {G | specNorm S * frobNorm T + frobNorm S * specNorm T +
        u * (specNorm S * specNorm T) < specNorm (S * G * T)} ≤
      Real.exp (-u ^ 2 / 2) := by
  exact gaussianMatrix_measureReal_gt_le_of_mean_le _
    (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    (add_nonneg (mul_nonneg (specNorm_nonneg _) (frobNorm_nonneg _))
      (mul_nonneg (frobNorm_nonneg _) (specNorm_nonneg _)))
    (by simp [specNorm_zero]) (abs_specNorm_mul_of_mul_sub_le S T)
    (integral_specNorm_mul_gaussianMatrix_mul_le S T) hu

end NLAlib

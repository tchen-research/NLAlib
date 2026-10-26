import NLAlib.RandomMatrix.Gaussian.Spectral.VarianceProfileProcessBound
import NLAlib.Probability.Gaussian.Moments.VarianceProfileRadii
import NLAlib.Probability.Gaussian.Moments.VarianceProfileCorrection

/-!
# A dimension-free Gaussian norm bound with a logarithmic row envelope

The nonlinear Gaussian process comparison and the logarithmic scalar
maximal estimate give a genuine expected operator-norm estimate from row
energies and logarithmically weighted row maxima. This weaker bound is
the estimate applied to the rapidly decaying remainder in the sharp
row-comparison theorem.

Source: van Handel, arXiv:1502.05003v4, Theorem 4.1; Latała--van
Handel--Youssef, arXiv:1711.00807v2, Theorem 3.8.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

variable {n : ℕ}

private theorem integral_radiusMaximum_eq_vector
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (∫ H, varianceProfileRadiusMaximum B H ∂gaussianMatrix (Fin 2) (Fin n)) =
      ∫ g, ‖fun i => varianceProfileRadius B g i‖ ∂gaussianVector (Fin n) := by
  have hF : AEStronglyMeasurable (fun g : Fin n → ℝ => ‖fun i => varianceProfileRadius B g i‖)
      (gaussianVector (Fin n)) := by
    apply Measurable.aestronglyMeasurable
    unfold varianceProfileRadius
    fun_prop
  exact (measurePreserving_gaussianMatrix_row (0 : Fin 2)).hasLaw.integral_comp
    hF

private theorem integral_correctionMaximum_eq_vector
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    (∫ H, varianceProfileCorrectionMaximum B hB H ∂gaussianMatrix (Fin 2) (Fin n)) =
      ∫ g, ‖fun i => ∑ k, spectralAbsoluteFactor hB i k * g k‖ ∂gaussianVector (Fin n) := by
  have hF : AEStronglyMeasurable (fun g : Fin n → ℝ =>
      ‖fun i => ∑ k, spectralAbsoluteFactor hB i k * g k‖) (gaussianVector (Fin n)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  exact (measurePreserving_gaussianMatrix_row (1 : Fin 2)).hasLaw.integral_comp hF

/-- A genuine dimension-free expected norm estimate for a symmetric
Gaussian matrix with bounded row energies and a logarithmic entry
envelope. The coefficient profile may have either sign. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_log_envelope
    (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm) (a d : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hrow : ∀ i, ∑ j, b i j ^ 2 ≤ a ^ 2)
    (hcap : ∀ i j, |b i j| * Real.log (((i : ℕ) : ℝ) + 2) ≤ d) :
    (∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix (Fin n) (Fin n)) ≤
      200 * (a + d) := by
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => b i j ^ 2
  let L : Fin n → ℝ := fun i => ‖b i‖
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => sq_nonneg _
  have hBH : B.IsHermitian := isHermitian_varianceProfile_sq b hb
  have hL0 (i : Fin n) : 0 ≤ L i := norm_nonneg _
  have hLsq (i j : Fin n) : b i j ^ 2 ≤ L i ^ 2 := by
    have h := norm_le_pi_norm (b i) j
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hLa (i : Fin n) : L i ≤ a := by
    have hnorm : L i ^ 2 ≤ ∑ j, b i j ^ 2 := by
      have hmax : L i ≤ Real.sqrt (∑ j, b i j ^ 2) := by
        apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
        intro j
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j))
      nlinarith [Real.sq_sqrt (show 0 ≤ ∑ j, b i j ^ 2 from
        Finset.sum_nonneg fun j _ => sq_nonneg (b i j)), hL0 i,
          Real.sqrt_nonneg (∑ j, b i j ^ 2)]
    nlinarith [hrow i, hL0 i]
  have hlog0 (i : Fin n) : 0 < Real.log (((i : ℕ) : ℝ) + 2) := by
    apply Real.log_pos
    have hi : 0 ≤ (((i : ℕ) : ℝ)) := Nat.cast_nonneg _
    linarith
  have hLd (i : Fin n) : L i * Real.log (((i : ℕ) : ℝ) + 2) ≤ d := by
    apply (le_div_iff₀ (hlog0 i)).mp
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hd (hlog0 i).le)).mpr
    intro j
    exact (le_div_iff₀ (hlog0 i)).mpr (hcap i j)
  have henv (i : Fin n) : L i ^ 2 * Real.log (((i : ℕ) : ℝ) + 2) ≤ (a + d) ^ 2 := by
    have hmul := mul_le_mul (hLa i) (hLd i) (mul_nonneg (hL0 i) (hlog0 i).le) ha
    nlinarith [mul_nonneg ha hd]
  have hfourth (i : Fin n) : Real.sqrt (∑ j, B i j ^ 2) ≤ a * L i := by
    apply (Real.sqrt_le_left (mul_nonneg ha (hL0 i))).mpr
    have hs : (∑ j, B i j ^ 2) ≤ L i ^ 2 * ∑ j, b i j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      dsimp [B]
      nlinarith [hLsq i j, sq_nonneg (b i j), sq_nonneg (L i)]
    have hm := mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (L i))
    nlinarith
  have henvC (i : Fin n) : Real.sqrt (∑ j, B i j ^ 2) *
      Real.log (((i : ℕ) : ℝ) + 2) ≤ (a + d) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right (hfourth i) (hlog0 i).le
    have hmul2 := mul_le_mul_of_nonneg_left (hLd i) ha
    nlinarith [mul_nonneg ha hd]
  rcases eq_or_lt_of_le (add_nonneg ha hd) with hz | hpos
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by
      ext i j
      have hs := (Finset.single_le_sum (fun k _ => sq_nonneg (b i k)) (Finset.mem_univ j)).trans (hrow i)
      rw [ha0] at hs
      change b i j = 0
      nlinarith
    subst b
    have heq (G : Matrix (Fin n) (Fin n) ℝ) : symmetricGaussianMatrix 0 G = 0 := by
      ext i j
      simp only [symmetricGaussianMatrix, Matrix.of_apply, Matrix.zero_apply, zero_mul]
    simp only [heq, specNorm_zero, integral_zero]
    exact mul_nonneg (by norm_num) (add_nonneg ha hd)
  · have hR := integral_norm_varianceProfileRadius_gaussianVector_le B hB0 L hL0
      (fun i j => hLsq i j) a (a + d) ha hpos hrow henv
    have hC := integral_norm_spectralAbsoluteFactor_mul_gaussianVector_le B hBH (a + d) hpos henvC
    have hnorm := integral_specNorm_symmetricGaussianMatrix_le_comparison_maxima b hb
    rw [integral_radiusMaximum_eq_vector, integral_correctionMaximum_eq_vector] at hnorm
    change (∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix (Fin n) (Fin n)) ≤
      8 * (∫ g, ‖fun i => varianceProfileRadius B g i‖ ∂gaussianVector (Fin n)) +
        4 * (∫ g, ‖fun i => ∑ k, spectralAbsoluteFactor hBH i k * g k‖ ∂gaussianVector (Fin n)) at hnorm
    linarith

end NLAlib

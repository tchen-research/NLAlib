import NLAlib.RandomMatrix.Gaussian.Basic.RowTailLower
import NLAlib.RandomMatrix.Gaussian.Basic.SchattenConcentration
import NLAlib.Probability.SubGaussian.TailComparison

/-!
# Transferring Gaussian Schatten mean comparison to all tails

The actual native Schatten norm and mixed row norm have the same centered
Gaussian proxy. One largest actual Gaussian entry supplies the required
row lower tail. Thus a dimension-free mean comparison implies the full
tail comparison, including zero profiles, empty dimensions, and infinity.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Corollary 1.4.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- For the actual symmetric Gaussian profile ensemble, an expected
Schatten-row comparison transfers to all upper tails with a universal
constant depending only on the expected-norm constant. -/
theorem measure_schattenNorm_le_mul_measure_rowMixedNorm_of_integral_le
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 2 ≤ p)
    {A : ℝ} (hA : 1 ≤ A)
    (hmean : (∫ G, schattenNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) ≤
      A * ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι)
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianMatrix ι ι).real {G | t ≤ schattenNorm (symmetricGaussianMatrix b G) p} ≤
      gaussianTailComparisonConstant A gaussianAbsoluteLowerConstant
        (Real.exp (-1) / Real.sqrt (2 * Real.pi)) *
      (gaussianMatrix ι ι).real {G |
        t / gaussianTailComparisonConstant A gaussianAbsoluteLowerConstant
          (Real.exp (-1) / Real.sqrt (2 * Real.pi)) ≤
            rowMixedNorm (symmetricGaussianMatrix b G) p} := by
  classical
  let m := ‖fun ij : ι × ι => b ij.1 ij.2‖
  have hc : 0 < Real.exp (-1) / Real.sqrt (2 * Real.pi) := by positivity
  have hC := hA.trans (le_gaussianTailComparisonConstant hA gaussianAbsoluteLowerConstant_pos hc)
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  by_cases hm0 : m = 0
  · have hbzero : b = 0 := by
      have hz := norm_eq_zero.mp hm0
      ext i j
      exact congrFun hz (i, j)
    have hsample (G : Matrix ι ι ℝ) : symmetricGaussianMatrix b G = 0 := by
      ext i j
      simp only [symmetricGaussianMatrix, hbzero, Matrix.of_apply, Matrix.zero_apply, zero_mul]
    have hS (G : Matrix ι ι ℝ) : schattenNorm (symmetricGaussianMatrix b G) p = 0 :=
      (schattenNorm_eq_zero_iff _ hp1).mpr (hsample G)
    have hR (G : Matrix ι ι ℝ) : rowMixedNorm (symmetricGaussianMatrix b G) p = 0 := by
      rw [hsample]
      exact rowMixedNorm_zero hp1
    by_cases ht0 : t = 0
    · subst t
      simpa only [hS, hR, zero_div, le_refl, Set.ofPred_true, probReal_univ, mul_one] using hC
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hleft : (gaussianMatrix ι ι).real
          {G | t ≤ schattenNorm (symmetricGaussianMatrix b G) p} = 0 := by
        simp only [hS, show ¬t ≤ 0 by linarith, Set.ofPred_false, measureReal_empty]
      rw [hleft]
      exact mul_nonneg (le_trans (by norm_num) hC) measureReal_nonneg
  · have hm : 0 < m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hm0)
    have hcap (i j : ι) : b i j ^ 2 ≤ m ^ 2 := by
      have h : |b i j| ≤ m := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm (fun ij : ι × ι => b ij.1 ij.2) (i, j)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    exact measure_ge_le_mul_measure_ge_div_of_gaussian_concentration
      hA gaussianAbsoluteLowerConstant_pos hc hm
      (hasSubgaussianMGF_schattenNorm_symmetricGaussianMatrix b hm.le hcap hp)
      (hasSubgaussianMGF_rowMixedNorm_symmetricGaussianMatrix b hm.le hcap hp)
      hmean (gaussianAbsoluteLowerConstant_mul_profile_scale_le_integral_rowMixedNorm b hb hp)
      (fun u hu => exp_neg_sq_div_sqrt_two_pi_le_measure_rowMixedNorm_symmetricGaussianMatrix
        b hb hp hm hu) ht

end NLAlib

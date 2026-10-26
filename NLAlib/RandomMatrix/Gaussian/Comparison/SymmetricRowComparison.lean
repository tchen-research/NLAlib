import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricRowMeanComparison
import NLAlib.RandomMatrix.Gaussian.Comparison.SymmetricRowTailComparison

/-!
# Full Gaussian Schatten-row comparison

For an actual symmetric Gaussian matrix, its Schatten norm and the mixed
norm of its Euclidean row lengths have comparable expectations and tails.
The same explicit universal constant applies to every native exponent at
least two, including infinity, and every finite nonnegative symmetric
coefficient profile. Empty dimensions and zero profiles are included.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Corollary 1.4.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLAlib

/-- One universal constant for both expectations and all tails in the
Gaussian Schatten-row comparison, independent of dimension and exponent. -/
def gaussianSchattenRowComparisonConstant : ℝ :=
  gaussianTailComparisonConstant gaussianRowMeanComparisonConstant
    gaussianAbsoluteLowerConstant (Real.exp (-1) / Real.sqrt (2 * Real.pi))

/-- The full Gaussian Schatten-row comparison. The actual Schatten and
mixed Euclidean-row norms have comparable expectations and upper tails,
uniformly over every real exponent at least two and infinity. All measures
refer to the genuine independent Gaussian lower-triangular construction.
Source: Latała--van Handel--Youssef, Corollary 1.4.
atlas: heterogeneous-gaussian-schatten-row-comparison -/
theorem gaussian_schatten_row_comparison
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ≥0∞} (hp : 2 ≤ p) :
    1 ≤ gaussianSchattenRowComparisonConstant ∧
    ((∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) ≤
      ∫ G, schattenNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) ∧
    ((∫ G, schattenNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) ≤
      gaussianSchattenRowComparisonConstant *
        ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) ∧
    ∀ t : ℝ, 0 ≤ t →
      (gaussianMatrix ι ι).real {G | t ≤ rowMixedNorm (symmetricGaussianMatrix b G) p} ≤
        (gaussianMatrix ι ι).real {G | t ≤ schattenNorm (symmetricGaussianMatrix b G) p} ∧
      (gaussianMatrix ι ι).real {G | t ≤ schattenNorm (symmetricGaussianMatrix b G) p} ≤
        gaussianSchattenRowComparisonConstant * (gaussianMatrix ι ι).real
          {G | t / gaussianSchattenRowComparisonConstant ≤
            rowMixedNorm (symmetricGaussianMatrix b G) p} := by
  have hA := one_le_gaussianRowMeanComparisonConstant
  have hc : 0 < Real.exp (-1) / Real.sqrt (2 * Real.pi) := by positivity
  have hAC : gaussianRowMeanComparisonConstant ≤ gaussianSchattenRowComparisonConstant :=
    le_gaussianTailComparisonConstant hA gaussianAbsoluteLowerConstant_pos hc
  have hmean := integral_schattenNorm_symmetricGaussianMatrix_le_integral_rowMixedNorm b hb hb0 hp
  refine ⟨hA.trans hAC, ?_, ?_, ?_⟩
  · exact integral_mono (integrable_rowMixedNorm_symmetricGaussianMatrix b hp)
      (integrable_schattenNorm_symmetricGaussianMatrix b hp)
      (fun G => rowMixedNorm_le_schattenNorm _ hp)
  · exact hmean.trans (mul_le_mul_of_nonneg_right hAC
      (integral_nonneg fun G => rowMixedNorm_nonneg _ _))
  · intro t ht
    refine ⟨measureReal_mono (fun G hG => hG.trans (rowMixedNorm_le_schattenNorm _ hp))
      (by finiteness), ?_⟩
    exact measure_schattenNorm_le_mul_measure_rowMixedNorm_of_integral_le b hb hp hA hmean ht

end NLAlib

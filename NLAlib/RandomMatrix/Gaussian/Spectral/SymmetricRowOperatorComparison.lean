import NLAlib.RandomMatrix.Gaussian.Spectral.SymmetricProfileOperatorMean
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricSelectedEntriesLower

/-!
# Expected Gaussian operator norm versus the actual maximum row norm

The sharp deterministic profile upper bound and both actual row lower
bounds give the infinity endpoint of the heterogeneous Gaussian
Schatten-row comparison. All constants are explicit and universal.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Corollary 1.4,
infinity-exponent expectation comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

/-- An explicit universal constant comparing the expected Gaussian
operator norm with the expected maximum Euclidean row norm. -/
def gaussianRowOperatorComparisonConstant : ℝ :=
  4096 * (gaussianAbsoluteLowerConstant⁻¹ + 2 / gaussianMaximumLowerConstant)

/-- The Gaussian operator-row comparison constant is strictly positive. -/
theorem gaussianRowOperatorComparisonConstant_pos : 0 < gaussianRowOperatorComparisonConstant := by
  unfold gaussianRowOperatorComparisonConstant
  have hκ := gaussianAbsoluteLowerConstant_pos
  have hc := gaussianMaximumLowerConstant_pos
  positivity

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The maximum deterministic row energy is bounded by the expected
actual maximum Gaussian row length, with a universal scalar constant. -/
theorem profileMaxRowEnergy_le_integral_rowMixedNorm_top
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) :
    profileMaxRowEnergy b ≤ gaussianAbsoluteLowerConstant⁻¹ *
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  have h := gaussianAbsoluteLowerConstant_mul_rowMixedNorm_le_integral b hb (p := ⊤) (by simp)
  have heq : rowMixedNorm b ⊤ = profileMaxRowEnergy b := by
    rw [rowMixedNorm_top_eq_pi_norm]
    simp only [profileMaxRowEnergy, rowSq, Real.norm_eq_abs, sq_abs]
  rw [heq] at h
  have hdiv : profileMaxRowEnergy b ≤
      (∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι) /
        gaussianAbsoluteLowerConstant := by
    apply (le_div_iff₀ gaussianAbsoluteLowerConstant_pos).mpr
    nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- The sorted logarithmic row-maximum profile is bounded by the expected
actual maximum Gaussian row length, after canonical duplicates are removed. -/
theorem profileLogRowMaximum_le_integral_rowMixedNorm_top
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j) :
    profileLogRowMaximum b ≤ (2 / gaussianMaximumLowerConstant) *
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  have h := gaussianMaximumLowerConstant_mul_profileLogRowMaximum_le_integral b hb hb0
  have hdiv : profileLogRowMaximum b ≤
      (2 * ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι) /
        gaussianMaximumLowerConstant := by
    apply (le_div_iff₀ gaussianMaximumLowerConstant_pos).mpr
    nlinarith
  convert hdiv using 1
  ring

/-- The actual expected Gaussian operator norm is bounded by a universal
constant times the actual expected maximum Euclidean row norm. Empty
dimensions and zero profiles are included. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_integral_rowMixedNorm_top
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j) :
    (∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix ι ι) ≤
      gaussianRowOperatorComparisonConstant *
        ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  apply (integral_specNorm_symmetricGaussianMatrix_le_profile_envelopes b hb hb0).trans
  have ha := profileMaxRowEnergy_le_integral_rowMixedNorm_top b hb
  have hm := profileLogRowMaximum_le_integral_rowMixedNorm_top b hb hb0
  dsimp [gaussianRowOperatorComparisonConstant]
  nlinarith

end NLAlib

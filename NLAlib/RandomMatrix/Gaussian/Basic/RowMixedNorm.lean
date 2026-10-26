import NLAlib.Matrix.Norms.RowMixedNorm
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileLipschitz
import NLAlib.Probability.SubGaussian.RealLpMoments

/-!
# Gaussian mixed-row norm concentration and real moments

The actual mixed row norm has the same `sqrt 2` entry-scale Lipschitz bound
as the spectral norm. Its centered MGF is sub-Gaussian, and every real
rooted moment is controlled by its actual mean and a square-root fluctuation.
Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace NLAlib

/-- Mixed row norms of the actual symmetric Gaussian sample have Frobenius
Lipschitz constant `sqrt 2 * m`, uniformly over native exponents at least two. -/
theorem abs_rowMixedNorm_symmetricGaussianMatrix_sub_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) {p : ℝ≥0∞} (hp : 2 ≤ p)
    (G H : Matrix ι ι ℝ) :
    |rowMixedNorm (symmetricGaussianMatrix b G) p -
      rowMixedNorm (symmetricGaussianMatrix b H) p| ≤
        Real.sqrt 2 * m * frobNorm (G - H) :=
  (abs_rowMixedNorm_sub_le_frobNorm _ _ hp).trans
    (frobNorm_symmetricGaussianMatrix_sub_le b hm hcap G H)

/-- The centered actual Gaussian mixed-row norm is sub-Gaussian with proxy
`2 m²`, for every native row exponent at least two, including infinity. -/
theorem hasSubgaussianMGF_rowMixedNorm_symmetricGaussianMatrix
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    HasSubgaussianMGF
      (fun G => rowMixedNorm (symmetricGaussianMatrix b G) p -
        ∫ H, rowMixedNorm (symmetricGaussianMatrix b H) p ∂gaussianMatrix ι ι)
      ⟨2 * m ^ 2, by positivity⟩ (gaussianMatrix ι ι) := by
  have hproxy : (Real.sqrt 2 * m) ^ 2 = 2 * m ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [hproxy] using hasSubgaussianMGF_of_lipschitz_gaussianMatrix
    (fun G => rowMixedNorm (symmetricGaussianMatrix b G) p) (Real.sqrt 2 * m)
    (mul_nonneg (Real.sqrt_nonneg _) hm)
    (abs_rowMixedNorm_symmetricGaussianMatrix_sub_le b hm hcap hp)

/-- Every finite real moment of the actual Gaussian mixed-row norm exists. -/
theorem memLp_rowMixedNorm_symmetricGaussianMatrix
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ)
    {p : ℝ≥0∞} (hp : 2 ≤ p) (q : ℝ≥0) :
    MemLp (fun G => rowMixedNorm (symmetricGaussianMatrix b G) p) q (gaussianMatrix ι ι) := by
  let m := ‖fun ij : ι × ι => b ij.1 ij.2‖
  have hm : 0 ≤ m := norm_nonneg _
  have hcap (i j : ι) : b i j ^ 2 ≤ m ^ 2 := by
    have h : |b i j| ≤ m := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun ij : ι × ι => b ij.1 ij.2) (i, j)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  exact memLp_of_centered_hasSubgaussianMGF
    (hasSubgaussianMGF_rowMixedNorm_symmetricGaussianMatrix b hm hcap hp) q

/-- The actual Gaussian mixed-row norm is integrable at every native row
exponent at least two, including infinity. -/
theorem integrable_rowMixedNorm_symmetricGaussianMatrix
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ)
    {p : ℝ≥0∞} (hp : 2 ≤ p) :
    Integrable (fun G => rowMixedNorm (symmetricGaussianMatrix b G) p) (gaussianMatrix ι ι) :=
  (memLp_rowMixedNorm_symmetricGaussianMatrix b hp 1).integrable (by simp)

/-- Every real rooted moment of a Gaussian mixed-row norm is at most its
actual mean plus `4 sqrt r * m`. The row exponent may independently be
finite or infinite, and zero entry scales are included. -/
theorem integral_rowMixedNorm_symmetricGaussianMatrix_rpow_root_le_integral_add
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) {p : ℝ≥0∞} (hp : 2 ≤ p)
    {r : ℝ} (hr : 2 ≤ r) :
    (∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ^ r ∂gaussianMatrix ι ι) ^ r⁻¹ ≤
      (∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι) +
        4 * Real.sqrt r * m := by
  have h := lpNorm_ofReal_le_integral_add_two_mul_sqrt_of_centered_hasSubgaussianMGF
    (fun G => rowMixedNorm_nonneg (symmetricGaussianMatrix b G) p)
    (hasSubgaussianMGF_rowMixedNorm_symmetricGaussianMatrix b hm hcap hp) hr
  rw [lpNorm_eq_integral_norm_rpow_toReal (by simp [show 0 < r by linarith])
    ENNReal.ofReal_ne_top
    (integrable_rowMixedNorm_symmetricGaussianMatrix b hp).aestronglyMeasurable] at h
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r by linarith),
    Real.norm_of_nonneg (rowMixedNorm_nonneg _ _)] at h
  apply h.trans
  refine add_le_add le_rfl ?_
  change 2 * Real.sqrt ((2 * m ^ 2) * r) ≤ 4 * Real.sqrt r * m
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) (sq_nonneg m)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hm]
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hsqrt
    (mul_nonneg hm (Real.sqrt_nonneg r))]

end NLAlib

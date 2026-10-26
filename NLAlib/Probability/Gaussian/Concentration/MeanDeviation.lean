import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration
import NLAlib.Probability.SubGaussian.Moments
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation
import NLAlib.ForMathlib.MeasureTheory.FiniteMaximumMean

/-!
# Mean deviations and maxima of Lipschitz Gaussian observables

Herbst's inequality bounds the mean absolute deviation by twice the Lipschitz
constant. A finite maximum is then controlled by a common mean bound and the
sum of the Lipschitz constants, without independence of the observables.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NLAlib

/-- A centered sub-Gaussian variable has mean absolute value at most twice
the square root of its variance proxy. The zero-proxy case is included. -/
theorem integral_abs_le_two_mul_sqrt_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    (∫ ω, |X ω| ∂μ) ≤ 2 * Real.sqrt (c : ℝ) := by
  have hi : Integrable (fun ω => |X ω| ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, sq_abs] using (h.memLp 2).integrable_sq
  have hm := integral_rpow_root_le_of_nonneg_of_le h.integrable.abs.aestronglyMeasurable
    (fun ω => abs_nonneg (X ω)) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 2) hi
  have hb := integral_abs_rpow_le_of_hasSubgaussianMGF h (by norm_num : (0 : ℝ) < 2)
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one,
    Real.Gamma_one, mul_one] at hb
  calc
    (∫ ω, |X ω| ∂μ) ≤ Real.sqrt (∫ ω, |X ω| ^ (2 : ℝ) ∂μ) := by
      simpa only [Real.rpow_one, inv_one, Real.sqrt_eq_rpow, one_div] using hm
    _ ≤ Real.sqrt (4 * (c : ℝ)) := Real.sqrt_le_sqrt (by linarith)
    _ = 2 * Real.sqrt (c : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- A Lipschitz function of a standard Gaussian vector has mean absolute
deviation at most twice its Euclidean Lipschitz constant. -/
theorem integral_abs_sub_integral_le_two_mul_of_lipschitz_gaussianVector
    {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    (∫ x, |f x - ∫ y, f y ∂gaussianVector ι| ∂gaussianVector ι) ≤ 2 * L := by
  classical
  have h := integral_abs_le_two_mul_sqrt_of_hasSubgaussianMGF
    (hasSubgaussianMGF_of_logSobolev hasEuclideanLogSobolev_gaussianVector f L hL hLip)
  change (∫ x, |f x - ∫ y, f y ∂gaussianVector ι| ∂gaussianVector ι) ≤
    2 * Real.sqrt (1 * L ^ 2) at h
  simpa only [one_mul, Real.sqrt_sq hL] using h

/-- A finite collection of Lipschitz Gaussian observables has maximum mean
bounded by a common mean bound plus twice the sum of the Lipschitz constants.
This version is useful when those constants decrease summably with the block. -/
theorem integral_iSup_le_mean_add_two_mul_sum_of_lipschitz_gaussianVector
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (f : κ → (ι → ℝ) → ℝ) (L : κ → ℝ) (hL : ∀ k, 0 ≤ L k)
    (hLip : ∀ k x y, |f k x - f k y| ≤ L k * Real.sqrt (∑ i, (x i - y i) ^ 2))
    {M : ℝ} (hM : ∀ k, ∫ x, f k x ∂gaussianVector ι ≤ M) :
    (∫ x, ⨆ k, f k x ∂gaussianVector ι) ≤ M + 2 * ∑ k, L k := by
  apply (integral_iSup_le_mean_add_sum_integral_abs_sub f
    (fun k => integrable_of_lipschitz_gaussianVector (f k) (L k) (hL k) (hLip k)) hM).trans
  gcongr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    integral_abs_sub_integral_le_two_mul_of_lipschitz_gaussianVector
      (f k) (L k) (hL k) (hLip k)

end NLAlib

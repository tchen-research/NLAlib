import NLAlib.ForMathlib.Probability.QuadraticCovariance
import Mathlib.Analysis.Complex.Norm

/-!
# Complex observation moments from full real covariance

Matching full real-coordinate means and covariances preserves squared
moduli of genuine complex linear observations, including singular laws.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {κ Ω Ω' : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Full real means and covariances identify the actual squared-modulus
expectation of every continuous complex observation. Mixed real/imaginary
covariances are retained, and no Gaussianity is needed. -/
theorem integral_norm_sq_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    {X : Ω → κ → ℝ} {Y : Ω' → κ → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 ν)
    (hmean : (∫ ω, X ω ∂μ) = ∫ ω, Y ω ∂ν)
    (hcov : ∀ i j, cov[(fun ω => X ω i), (fun ω => X ω j); μ] =
      cov[(fun ω => Y ω i), (fun ω => Y ω j); ν])
    (L : (κ → ℝ) →L[ℝ] ℂ) :
    (∫ ω, ‖L (X ω)‖ ^ 2 ∂μ) = ∫ ω, ‖L (Y ω)‖ ^ 2 ∂ν := by
  let R := Complex.reCLM.comp L
  let I := Complex.imCLM.comp L
  let B := (ContinuousLinearMap.mul ℝ ℝ).bilinearComp R R +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp I I
  have hB (x : κ → ℝ) : B x x = ‖L x‖ ^ 2 := by
    change (L x).re * (L x).re + (L x).im * (L x).im = ‖L x‖ ^ 2
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hm (i : κ) : (∫ ω, X ω i ∂μ) = ∫ ω, Y ω i ∂ν := by
    let P : (κ → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (P.integral_comp_comm (hX.integrable one_le_two)).trans
      ((congrArg P hmean).trans (P.integral_comp_comm (hY.integrable one_le_two)).symm)
  have hs := NLAlib.integral_mul_coordinates_eq_of_mean_covariance_eq hX hY hm hcov
  have h := NLAlib.integral_bilin_quadratic_eq_of_second_moments_eq B hX hY hs
  simpa only [hB] using h

end MeasureTheory

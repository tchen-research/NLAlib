import NLAlib.Probability.Concentration.Matrix.GaussianResolventLaw
import NLAlib.Probability.SubGaussian.LpMoments
import NLAlib.Probability.Transforms.ResolventNormMoments

/-!
# Actual Gaussian resolvent moments and realizations

Actual Gaussian concentration controls the even Lp norm and its difference
from a realized resolvent norm. The original bilinear variance budget is
retained. Source: arXiv:2201.05142v3, Lemmas 5.5 and 7.3.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The genuine Gaussian resolvent Lp norm is controlled by its actual
expectation and the bilinear Gaussian variance budget, uniformly in its mean.
Zero variance and empty matrix shapes are included. -/
theorem lpNorm_specNorm_resolvent_add_gaussian_le_integral_add_sqrt
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ (Z *ᵥ w)‖ ^ 2 ∂γ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    lpNorm (fun Z => specNorm (resolvent (D + Z) ζ)) (2 * (p : ℝ≥0∞)) γ ≤
      (∫ Z, specNorm (resolvent (D + Z) ζ) ∂γ) +
        Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) := by
  exact lpNorm_le_integral_add_sqrt_of_centered_hasSubgaussianMGF
    (fun _ => specNorm_nonneg _)
    (hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_bilinear_second_moment
      γ D hD hHerm hmean hσ hbilinear ζ hζ) hp

open scoped Matrix.Norms.L2Operator in
/-- Outside an actual Gaussian tail the realized resolvent norm controls
its even Lp norm. The estimate imposes no positivity on the variance budget. -/
theorem measureReal_lpNorm_specNorm_resolvent_add_gaussian_gt_le
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ (Z *ᵥ w)‖ ^ 2 ∂γ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    γ.real {Z | specNorm (resolvent (D + Z) ζ) +
      Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) +
        (σ * (|ζ.im|⁻¹) ^ 2) * t <
      lpNorm (fun H => specNorm (resolvent (D + H) ζ)) (2 * (p : ℝ≥0∞)) γ} ≤
        2 * Real.exp (-t ^ 2 / 2) := by
  have hm := lpNorm_specNorm_resolvent_add_gaussian_le_integral_add_sqrt
    γ D hD hHerm hmean hσ hbilinear ζ hζ hp
  apply (measureReal_mono (μ := γ) (fun Z hZ => ?_)).trans
    (measureReal_lt_abs_specNorm_resolvent_add_gaussian_sub_mean_le
      γ D hD hHerm hmean hσ hbilinear ζ hζ ht)
  change (σ * (|ζ.im|⁻¹) ^ 2) * t <
    |specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ|
  change specNorm (resolvent (D + Z) ζ) +
    Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) +
      (σ * (|ζ.im|⁻¹) ^ 2) * t <
    lpNorm (fun H => specNorm (resolvent (D + H) ζ)) (2 * (p : ℝ≥0∞)) γ at hZ
  have hs := neg_le_abs (specNorm (resolvent (D + Z) ζ) -
    ∫ H, specNorm (resolvent (D + H) ζ) ∂γ)
  linarith

end NLAlib

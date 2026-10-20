import NLAlib.Probability.Concentration.Matrix.FiniteHermitianBernsteinTail
import NLAlib.Probability.Concentration.Matrix.GaussianMatrixLocalization
import NLAlib.Probability.Moments.BilinearSumCovariance
import NLAlib.Probability.Moments.BilinearVarianceNorm

/-!
# A shared localization scale for an independent sum and its Gaussian proxy

The original increments' bilinear variance bounds both actual spectra in
the same deterministic neighborhood of their common mean. Gaussian entry
covariances may be singular, and the mean is arbitrary.
Source: arXiv:2201.05142v3, Section 7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
/-- The original independent centered Hermitian sum has a localization
tail at a scale determined by its actual bilinear variance budget. The
matrix variance is derived from the original marginal moments.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_sum_pi_gt_bilinear_scale_le
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    {R s p : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) (hp : 0 < p)
    (hscale : 0 < R+s) (hd : 1 ≤ Fintype.card n)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (hmean : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ A : M, ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i) ≤ s^2) :
    (Measure.pi ν).real {x : ι → M |
      4*(Fintype.card n : ℝ)*(s*Real.sqrt p+R*p) < specNorm (∑ i, x i)} ≤
        (2*Fintype.card n : ℝ)*Real.exp (-p) := by
  have hn : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  let := hn
  have hdR : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hd
  have hQ : specNorm (∑ i, ∫ A : M, A^2 ∂ν i) ≤
      ((Fintype.card n : ℝ)*s)^2 := by
    have hh := specNorm_sum_integral_sq_le_card_sq_mul_of_bilinear_budget
      ν (fun _ (A : M) => A) (fun _ => measurable_id) hR hHerm hBound hbilinear
    nlinarith only [hh]
  have hscale' : 0 < (Fintype.card n : ℝ)*s+R := by nlinarith only [hscale,hdR,hs]
  have hraw := measureReal_specNorm_sum_pi_gt_four_sqrt_add_le
    ν (fun _ (A : M) => A) (fun _ => measurable_id) hR
      (mul_nonneg (Nat.cast_nonneg _) hs) hp hscale' hHerm hBound hmean hQ
  have hthreshold : 4*((Fintype.card n : ℝ)*s)*Real.sqrt p+4*R*p ≤
      4*(Fintype.card n : ℝ)*(s*Real.sqrt p+R*p) := by
    have hh := mul_le_mul_of_nonneg_right hdR (by positivity : 0 ≤ 4*R*p)
    linear_combination hh
  apply (measureReal_mono (μ := Measure.pi ν) ?_).trans hraw
  intro x hx
  exact lt_of_le_of_lt hthreshold hx

open scoped Matrix.Norms.L2Operator in
/-- Full covariance matching derives the actual centered Gaussian
localization tail from the original increments' bilinear variance budget.
No entry independence or nonsingular covariance is assumed.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_gaussian_sub_mean_gt_bilinear_scale_le
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    {R s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (hmean : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ A : M, ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i) ≤ s^2)
    (ρ : Measure M) [IsGaussian ρ]
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν]) :
    ρ.real {A : M | 4*(Fintype.card n : ℝ)*s*Real.sqrt p <
      specNorm (A-∫ B : M,B ∂ρ)} ≤ 4*(Fintype.card n : ℝ)^2*Real.exp (-p) := by
  have hbudget (a b : EuclideanSpace ℂ n) (ha : ‖a‖=1) (hb : ‖b‖=1) :
      (∫ A : M, ‖star a.ofLp ⬝ᵥ ((A-∫ B : M,B ∂ρ) *ᵥ b.ofLp)‖^2 ∂ρ) ≤ s^2 := by
    rw [integral_norm_sq_centered_bilinear_eq_sum_of_covariance_eq
      ν (fun _ (A : M) => A) (fun _ => measurable_id) hBound hmean
        ρ IsGaussian.memLp_two_id hcov]
    exact hbilinear a b ha.le hb.le
  simpa only [Real.sqrt_sq hs] using
    measureReal_centered_specNorm_gt_le_gaussian_of_bilinear_budget
      ρ (sq_nonneg s) hp hbudget

end NLAlib

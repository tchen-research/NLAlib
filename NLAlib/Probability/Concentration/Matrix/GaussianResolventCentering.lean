import NLAlib.Probability.Concentration.Matrix.GaussianResolventMoments
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional

/-!
# Resolvent concentration for noncentered Gaussian matrix laws

Centering the actual Gaussian matrix law transports the original bilinear
variance budget. No choice of Gaussian coordinates or supplied concentration
bound enters the public statements. Source: arXiv:2201.05142v3, Lemma 5.5.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The centered resolvent norm under a genuine, possibly noncentered,
Gaussian matrix law is sub-Gaussian with its actual bilinear variance budget.
Singular covariance and empty matrix shapes are included. -/
theorem hasSubgaussianMGF_specNorm_resolvent_gaussian_of_centered_bilinear_moment
    (ρ : Measure M) [IsGaussian ρ] (hHerm : ∀ᵐ Z ∂ρ, Z.IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ ((Z - ∫ H, H ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    HasSubgaussianMGF
      (fun Z => specNorm (resolvent Z ζ) - ∫ H, specNorm (resolvent H ζ) ∂ρ)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ ρ := by
  let D : M := ∫ Z, Z ∂ρ
  let γ := ρ.map (fun Z => Z-D)
  have hshift : AEMeasurable (fun Z : M => Z-D) ρ := by fun_prop
  have hD : D.IsHermitian := Matrix.isHermitian_integral hHerm
  have hγ : IsGaussian γ := by dsimp [γ]; infer_instance
  let := hγ
  have hγHerm : ∀ᵐ Z ∂γ, Z.IsHermitian := by
    have hm : MeasurableSet {Z : M | Z.IsHermitian} :=
      (isClosed_eq (by fun_prop : Continuous (fun Z : M => Zᴴ)) continuous_id).measurableSet
    apply (ae_map_iff hshift hm).mpr
    exact hHerm.mono fun Z hZ => hZ.sub hD
  have hγmean : (∫ Z, Z ∂γ) = 0 := by
    change (∫ Z : M, id Z ∂ρ.map (fun Z => Z-D)) = 0
    rw [integral_map hshift aestronglyMeasurable_id]
    change (∫ Z, Z-D ∂ρ) = 0
    rw [integral_sub (f := fun Z : M => Z) (g := fun _ : M => D)
      IsGaussian.integrable_id (integrable_const D), integral_const,
      probReal_univ, one_smul]
    exact sub_self _
  have hγbilinear : ∀ v w : n → ℂ,
      ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
        (∫ Z, ‖star v ⬝ᵥ (Z *ᵥ w)‖ ^ 2 ∂γ) ≤ σ ^ 2 := by
    intro v w hv hw
    rw [integral_map hshift]
    · exact hbilinear v w hv hw
    · exact (Matrix.bilinearCLM v w).continuous.measurable.norm.pow_const 2
        |>.aestronglyMeasurable
  have he (Z : M) : D+(Z-D)=Z := by abel
  have hobs : (∫ Z, specNorm (resolvent (D+Z) ζ) ∂γ) =
      ∫ Z, specNorm (resolvent Z ζ) ∂ρ := by
    rw [integral_map hshift]
    · simp only [he]
    · exact (((measurable_matrix_resolvent ζ).comp
        (measurable_const.add measurable_id)).norm).aestronglyMeasurable
  have hsg := hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_bilinear_second_moment
    γ D hD hγHerm hγmean hσ hγbilinear ζ hζ
  have hpull := HasSubgaussianMGF.of_map hshift hsg
  simpa only [Function.comp_def, he, hobs] using hpull

open scoped Matrix.Norms.L2Operator in
/-- The actual even Lp norm of a noncentered Gaussian resolvent is bounded
by its actual mean and the original centered bilinear variance budget. -/
theorem lpNorm_specNorm_resolvent_gaussian_le_integral_add_sqrt
    (ρ : Measure M) [IsGaussian ρ] (hHerm : ∀ᵐ Z ∂ρ, Z.IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ ((Z - ∫ H, H ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    lpNorm (fun Z => specNorm (resolvent Z ζ)) (2 * (p : ℝ≥0∞)) ρ ≤
      (∫ Z, specNorm (resolvent Z ζ) ∂ρ) +
        Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) := by
  exact lpNorm_le_integral_add_sqrt_of_centered_hasSubgaussianMGF
    (fun _ => specNorm_nonneg _)
    (hasSubgaussianMGF_specNorm_resolvent_gaussian_of_centered_bilinear_moment
      ρ hHerm hσ hbilinear ζ hζ) hp

end NLAlib

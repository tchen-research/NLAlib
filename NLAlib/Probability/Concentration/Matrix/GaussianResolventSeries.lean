import NLAlib.Matrix.Functions.HermitianResolventLipschitz
import NLAlib.Probability.Concentration.Matrix.GaussianMaximum

/-!
# Actual Gaussian resolvent-norm concentration from coefficient energy

The actual standard Gaussian coefficient law and its proved Euclidean LSI
supply the centered MGF, including zero variance and empty matrix shapes.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 5.5.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The centered native resolvent spectral norm of a Hermitian standard
Gaussian coefficient series has the actual sharp inverse-height MGF budget.
The zero-energy and empty-family or empty-matrix cases are included. -/
theorem hasSubgaussianMGF_specNorm_resolvent_affineSeries_of_quadratic_energy
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    HasSubgaussianMGF
      (fun x : ι → ℝ => specNorm (resolvent (D + ∑ i, x i • A i) ζ) -
        ∫ y, specNorm (resolvent (D + ∑ i, y i • A i) ζ) ∂gaussianVector ι)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ (gaussianVector ι) := by
  have he : (σ * (|ζ.im|⁻¹) ^ 2) ^ 2 = σ ^ 2 * (|ζ.im|⁻¹) ^ 4 := by ring
  simpa only [one_mul, he] using hasSubgaussianMGF_of_logSobolev
    hasEuclideanLogSobolev_gaussianVector
    (fun x : ι → ℝ => specNorm (resolvent (D + ∑ i, x i • A i) ζ))
    (σ * (|ζ.im|⁻¹) ^ 2) (by positivity)
    (abs_specNorm_resolvent_affineSeries_sub_le_of_quadratic_energy D hD A hA hσ henergy ζ hζ)

/-- The same actual Gaussian resolvent-norm MGF stated through actual
quadratic-form variances, rather than a supplied coefficient realization of
those variances. The source bilinear sigma-star budget bounds these unit-vector
quadratic variances by restriction to equal unit vectors. -/
theorem hasSubgaussianMGF_specNorm_resolvent_affineSeries_of_quadratic_variance
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun x : ι → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector ι] ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    HasSubgaussianMGF
      (fun x : ι → ℝ => specNorm (resolvent (D + ∑ i, x i • A i) ζ) -
        ∫ y, specNorm (resolvent (D + ∑ i, y i • A i) ζ) ∂gaussianVector ι)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ (gaussianVector ι) := by
  apply hasSubgaussianMGF_specNorm_resolvent_affineSeries_of_quadratic_energy
    D hD A hA hσ _ ζ hζ
  simpa only [variance_re_quadForm_gaussianSeries] using hvariance

end NLAlib

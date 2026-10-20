import NLAlib.Matrix.Spectral.HausdorffSpectrum
import NLAlib.Matrix.Norms.BilinearSphereParameters
import NLAlib.Probability.Gaussian.Concentration.MedianMean

/-! # Actual Gaussian spectral-distance concentration -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

/-- The actual Gaussian-series spectral distance to any fixed real set has the Euclidean coefficient Lipschitz bound from its unit quadratic energy. -/
theorem abs_hausdorffDist_spectrum_affineSeries_sub_le_of_quadratic_energy
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S : Set ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : d → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) (x y : ι → ℝ) :
    |Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S -
      Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, y i • A i)) S| ≤
        σ * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  classical
  have hs (x : ι → ℝ) : (∑ i, x i • A i).IsHermitian :=
    isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _)
  have hx := hA₀.add (hs x)
  have hy := hA₀.add (hs y)
  have hd : (A₀ + ∑ i, x i • A i) - (A₀ + ∑ i, y i • A i) =
      ∑ i, (x i - y i) • A i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  refine (abs_hausdorffDist_spectrum_sub_le_specNorm_sub hx hy S).trans ?_
  rw [hd]
  exact specNorm_sum_smul_le_of_quadratic_energy A hA hσ henergy _

/-- The literal attained bilinear coefficient variance controls the true spectral-distance observable at every pair of samples. -/
theorem abs_hausdorffDist_spectrum_affineSeries_sub_le_bilinearSquareMass
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S : Set ℝ) (x y : ι → ℝ) :
    |Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S -
      Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, y i • A i)) S| ≤
        Real.sqrt (bilinearSquareMass A Finset.univ) *
          Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  classical
  apply abs_hausdorffDist_spectrum_affineSeries_sub_le_of_quadratic_energy A₀ hA₀ A hA S
    (Real.sqrt_nonneg _)
  intro u hu
  rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _)]
  exact sum_re_quadForm_sq_le_bilinearSquareMass A u hu

/-- An actual half-probability spectral-distance bound controls the true expected spectral distance at the literal coefficient sigma-star scale. -/
theorem integral_hausdorffDist_spectrum_affineSeries_le_of_half_measure
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S : Set ℝ) (hpos : 0 < bilinearSquareMass A Finset.univ) {a : ℝ}
    (hhalf : (1 / 2 : ℝ) ≤ (gaussianVector ι).real
      {x | Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S ≤ a}) :
    (∫ x : ι → ℝ, Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S
      ∂gaussianVector ι) ≤ a + 4 * Real.sqrt (bilinearSquareMass A Finset.univ) := by
  apply integral_le_of_half_measure_sublevel_gaussianVector _ (Real.sqrt_pos.mpr hpos)
    (fun x y => abs_hausdorffDist_spectrum_affineSeries_sub_le_bilinearSquareMass A₀ hA₀ A hA S x y) hhalf

/-- An actual half-probability spectral-distance bound gives the all-height Gaussian tail at the literal sigma-star scale. The half-probability premise is discharged separately by a spectral grid comparison.
Source: arXiv:2406.11453v2, Theorem 2.2, Gaussian concentration step.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_hausdorffDist_spectrum_affineSeries_gt_of_half_measure
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S : Set ℝ) (hpos : 0 < bilinearSquareMass A Finset.univ) {a : ℝ}
    (hhalf : (1 / 2 : ℝ) ≤ (gaussianVector ι).real
      {x | Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S ≤ a})
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianVector ι).real
      {x | a + 4 * Real.sqrt (bilinearSquareMass A Finset.univ) +
          2 * Real.sqrt (bilinearSquareMass A Finset.univ) * t <
        Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i)) S} ≤ Real.exp (-t^2) := by
  apply measureReal_gt_sublevel_add_le_gaussianVector _ (Real.sqrt_pos.mpr hpos)
    (fun x y => abs_hausdorffDist_spectrum_affineSeries_sub_le_bilinearSquareMass A₀ hA₀ A hA S x y) hhalf ht

end NLAlib

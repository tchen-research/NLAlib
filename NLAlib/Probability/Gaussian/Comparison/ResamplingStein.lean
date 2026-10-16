import NLAlib.Probability.Gaussian.Comparison.ResamplingAffine
import NLAlib.Probability.Gaussian.Comparison.ResamplingQuadratic
import NLAlib.Probability.Gaussian.Calculus.AffineProductIntegrationByParts

/-!
# Exact resampling and Gaussian Stein cancellations

The first identity is discrete integration by parts on the actual resampling
triple. The second combines the actual Gaussian covariance, the complete
resampling covariance tensor, and independence of the second replacement.
No cancellation or interpolation identity is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype κ] [DecidableEq κ] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first exact source cancellation, with the actual triple and independent
noise law. The bounded continuous test needs no derivative hypothesis here.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_resamplingStein_first
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ] (a b : ℝ)
    (f : (κ → ℝ) → F) (hfc : Continuous f) (C : ℝ) (hfb : ∀ x, ‖f x‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    (∫ q, B (resamplingTripleOriginal q.1 - μ)
      (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2))
      ∂(resamplingTripleMeasure ν).prod γ) =
      ((Fintype.card ι : ℝ) / 2) •
        ∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
          (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
            f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
          ∂(resamplingTripleMeasure ν).prod γ :=
  integral_bilin_resamplingAffine ν hν γ a b f hfc C hfb B

/-- The second exact source cancellation. A centered Gaussian vector with the
actual original sum's full covariance contracts into the genuine resampling
difference and the independent second-replacement derivative test. Both sides
are genuine integrals; boundedness and second moments supply integrability.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_resamplingStein_gaussian
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : κ → ℝ => z i), (fun z : κ → ℝ => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (a b : ℝ) (f : (κ → ℝ) → F) (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F)
    (hf : ∀ y, HasFDerivAt f (df y) y) (hdf : Continuous df)
    (C C' : ℝ) (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    (∫ q, B q.2 (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2))
      ∂(resamplingTripleMeasure ν).prod γ) =
      (b * (Fintype.card ι : ℝ) / 2) •
        ∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
          (df (resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2)
            (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1))
          ∂(resamplingTripleMeasure ν).prod γ := by
  haveI := hγ.isProbabilityMeasure
  dsimp only
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  have hX : AEMeasurable (resamplingTripleOriginal : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) P :=
    (memLp_resamplingTriple_sums ν hν).1.aestronglyMeasurable.aemeasurable
  have hg := integral_bilin_gaussian_affine_product P resamplingTripleOriginal hX γ hγ hmean
    μ a b f df hf hdf C C' hfb hdfb B
  simp_rw [hcov, covariance_resamplingTripleOriginal_eval ν hν] at hg
  have hquad := integral_bilin_quadratic_resamplingTriple_affine ν hν γ μ a b df hdf C' hdfb B
  change (∫ q, B q.2 (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2))
    ∂P.prod γ) = _
  calc
    _ = b • ∑ i, ∑ j,
        (((Fintype.card ι : ℝ) / 2) *
          ∫ p, (resamplingTripleOriginal p i - resamplingTripleFirst p i) *
            (resamplingTripleOriginal p j - resamplingTripleFirst p j) ∂P) •
        ∫ q, B (Pi.single i 1)
          (df (μ + a • (resamplingTripleOriginal q.1 - μ) + b • q.2) (Pi.single j 1))
          ∂P.prod γ := by simpa only [resamplingAffinePoint] using hg
    _ = (b * (Fintype.card ι : ℝ) / 2) • ∑ i, ∑ j,
        (∫ p, (resamplingTripleOriginal p i - resamplingTripleFirst p i) *
          (resamplingTripleOriginal p j - resamplingTripleFirst p j) ∂P) •
        ∫ q, B (Pi.single i 1)
          (df (μ + a • (resamplingTripleOriginal q.1 - μ) + b • q.2) (Pi.single j 1))
          ∂P.prod γ := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    _ = _ := by rw [← hquad]; rfl

end NLAlib

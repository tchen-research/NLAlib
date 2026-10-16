import NLAlib.Probability.Gaussian.Calculus.BilinearIntegrationByParts
import NLAlib.ForMathlib.Analysis.FiniteCoordinateDerivative

/-!
# Bilinear Gaussian Stein identity for an affine test

This is the exact Gaussian term in a resampling comparison. The bounded C¹
test is composed with a fixed affine point; the chain rule gives precisely
the scalar coefficient on the covariance contraction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Gaussian affine bilinear test is integrable from its global bound and
the actual Gaussian first moment. -/
theorem integrable_bilin_gaussian_affine
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (μ x : κ → ℝ) (a b : ℝ) (f : (κ → ℝ) → F)
    (hfc : Continuous f) (C : ℝ) (hfb : ∀ y, ‖f y‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    Integrable (fun z => B z (f (μ + a • (x - μ) + b • z))) γ :=
  integrable_bilin_comp_of_hasGaussianLaw id hγ
    (fun z => f (μ + a • (x - μ) + b • z))
    (hfc.comp (by fun_prop)) C (fun z => hfb _) B

/-- The affine Gaussian Stein identity with the actual full real-coordinate
covariance. Centering is required only of the Gaussian vector. Boundedness of
the test and of its continuous derivative supplies every integral.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_gaussian_affine
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (μ x : κ → ℝ) (a b : ℝ)
    (f : (κ → ℝ) → F) (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F)
    (hf : ∀ y, HasFDerivAt f (df y) y) (hdf : Continuous df)
    (C C' : ℝ) (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    (∫ z, B z (f (μ + a • (x - μ) + b • z)) ∂γ) =
      b • ∑ i, ∑ j, cov[(fun z : κ → ℝ => z i), (fun z : κ → ℝ => z j); γ] •
        ∫ z, B (Pi.single i 1) (df (μ + a • (x - μ) + b • z) (Pi.single j 1)) ∂γ := by
  haveI := hγ.isProbabilityMeasure
  let g : (κ → ℝ) → F := fun z => f (μ + a • (x - μ) + b • z)
  let g' : κ → (κ → ℝ) → F := fun j z =>
    b • df (μ + a • (x - μ) + b • z) (Pi.single j 1)
  have hg (z : κ → ℝ) : HasFDerivAt g
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight
        (g' j z)) z := by
    have hA : HasFDerivAt (fun w : κ → ℝ => μ + a • (x - μ) + b • w)
        (b • ContinuousLinearMap.id ℝ (κ → ℝ)) z := by
      simpa using (hasFDerivAt_const (𝕜 := ℝ) (μ + a • (x - μ)) z).add
        ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul b)
    have h := (hf (μ + a • (x - μ) + b • z)).comp z hA
    have he : (df (μ + a • (x - μ) + b • z)).comp
        (b • ContinuousLinearMap.id ℝ (κ → ℝ)) =
        ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight
          (g' j z) := by
      symm
      convert ContinuousLinearMap.sum_proj_smulRight
        ((df (μ + a • (x - μ) + b • z)).comp
          (b • ContinuousLinearMap.id ℝ (κ → ℝ))) using 1
      simp [g', ContinuousLinearMap.comp_apply]
    rw [he] at h
    exact h
  have hg'c (j : κ) : Continuous (g' j) := by
    dsimp [g']
    exact ((hdf.comp (by fun_prop)).clm_apply continuous_const).const_smul b
  have hg'b (j : κ) (z : κ → ℝ) : ‖g' j z‖ ≤ |b| * C' := by
    dsimp [g']
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := ((df (μ + a • (x - μ) + b • z)).le_opNorm (Pi.single j 1)).trans
      (mul_le_mul_of_nonneg_right (hdfb _) (norm_nonneg _))
    simpa only [Pi.norm_single, norm_one, mul_one] using h
  have h := integral_bilin_eq_sum_covariance_smul_integral_of_hasGaussianLaw id hγ hmean
    g g' hg hg'c C (|b| * C') (fun z => hfb _) hg'b B
  simpa only [id_eq, g, g', map_smul, integral_smul, Finset.smul_sum, smul_smul,
    mul_comm b] using h

end NLAlib

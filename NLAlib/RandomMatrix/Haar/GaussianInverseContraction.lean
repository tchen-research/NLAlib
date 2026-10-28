import NLAlib.RandomMatrix.Haar.GaussianContraction
import NLAlib.RandomMatrix.Gaussian.InverseMoments.Mean
import NLAlib.RandomMatrix.Gaussian.InverseMoments.ComplexMean
import NLAlib.RandomMatrix.Gaussian.Moments.Conditioning
import NLAlib.RandomMatrix.Gaussian.Moments.ComplexSecondMoment

/-!
# Exact independent-block inverse moments for Haar normalization

The real and circular-complex native Gaussian laws give the exact finite mean
of the lower-block term after canonical QR. The factor two in the complex
Gaussian sandwich cancels its inverse-Wishart factor two.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib

/-- Native real independent-block contraction, with its actual integrability. -/
theorem integrable_and_integral_frobSq_gaussian_mul_pinvR_adjoint_prod
    {r ell s : ℕ} (hr : r+2 ≤ ell) :
    Integrable (fun p : Matrix (Fin r) (Fin ell) ℝ × Matrix (Fin s) (Fin r) ℝ =>
      frobSq (p.2*(pinvR p.1)ᴴ))
        ((gaussianMatrix (Fin r) (Fin ell)).prod (gaussianMatrix (Fin s) (Fin r))) ∧
    ∫ p : Matrix (Fin r) (Fin ell) ℝ × Matrix (Fin s) (Fin r) ℝ,
      frobSq (p.2*(pinvR p.1)ᴴ)
        ∂(gaussianMatrix (Fin r) (Fin ell)).prod (gaussianMatrix (Fin s) (Fin r)) =
          (s:ℝ)*r/((ell:ℝ)-r-1) := by
  have hi := integrable_and_integral_frobSq_pinvR_gaussianMatrix hr
  have hOne : frobSq (1 : Matrix (Fin s) (Fin s) ℝ) = (s:ℝ) := by
    rw [← Matrix.diagonal_one,frobSq_diagonal]
    simp
  have hfix (T : Matrix (Fin r) (Fin ell) ℝ) :
      Integrable (fun Z => frobSq (Z*T)) (gaussianMatrix (Fin s) (Fin r)) ∧
        ∫ Z, frobSq (Z*T) ∂gaussianMatrix (Fin s) (Fin r) = (s:ℝ)*frobSq T := by
    constructor
    · simpa only [Matrix.one_mul] using
        integrable_frobSq_mul_gaussianMatrix_mul (1 : Matrix (Fin s) (Fin s) ℝ) T
    · simpa only [Matrix.one_mul,hOne] using
        integral_frobSq_mul_gaussianMatrix_mul (1 : Matrix (Fin s) (Fin s) ℝ) T
  have h := integrable_and_integral_frobSq_mul_random_prod
    (fun X : Matrix (Fin r) (Fin ell) ℝ => (pinvR X)ᴴ)
    (Matrix.measurable_conjTranspose.comp measurable_pinvR)
    (by simpa only [frobSq_conjTranspose] using hi.1) (s:ℝ) hfix
  refine ⟨h.1,h.2.trans ?_⟩
  simp_rw [frobSq_conjTranspose]
  rw [hi.2]
  ring

/-- Native circular-complex independent-block contraction. Its factor two
cancels exactly, yielding the complex Haar denominator `ell-r`.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_complexGaussian_mul_pinvR_adjoint_prod
    {r ell s : ℕ} (hr : r+1 ≤ ell) :
    Integrable (fun p : Matrix (Fin r) (Fin ell) ℂ × Matrix (Fin s) (Fin r) ℂ =>
      frobSq (p.2*(pinvR p.1)ᴴ))
        ((circularComplexGaussianMatrix (Fin r) (Fin ell)).prod
          (circularComplexGaussianMatrix (Fin s) (Fin r))) ∧
    ∫ p : Matrix (Fin r) (Fin ell) ℂ × Matrix (Fin s) (Fin r) ℂ,
      frobSq (p.2*(pinvR p.1)ᴴ)
        ∂(circularComplexGaussianMatrix (Fin r) (Fin ell)).prod
          (circularComplexGaussianMatrix (Fin s) (Fin r)) =
          (s:ℝ)*r/((ell:ℝ)-r) := by
  have hi := integrable_and_integral_frobSq_pinvR_circularComplexGaussianMatrix hr
  have hOne : frobSq (1 : Matrix (Fin s) (Fin s) ℂ) = (s:ℝ) := by
    rw [← Matrix.diagonal_one,frobSq_diagonal]
    simp
  have hfix (T : Matrix (Fin r) (Fin ell) ℂ) :
      Integrable (fun Z => frobSq (Z*T)) (circularComplexGaussianMatrix (Fin s) (Fin r)) ∧
        ∫ Z, frobSq (Z*T) ∂circularComplexGaussianMatrix (Fin s) (Fin r) = (2*(s:ℝ))*frobSq T := by
    simpa only [Matrix.one_mul,hOne] using
      integrable_and_integral_frobSq_mul_circularComplexGaussianMatrix_mul
        (1 : Matrix (Fin s) (Fin s) ℂ) T
  have h := integrable_and_integral_frobSq_mul_random_prod
    (fun X : Matrix (Fin r) (Fin ell) ℂ => (pinvR X)ᴴ)
    (Matrix.measurable_conjTranspose.comp measurable_pinvR)
    (by simpa only [frobSq_conjTranspose] using hi.1) (2*(s:ℝ)) hfix
  refine ⟨h.1,h.2.trans ?_⟩
  simp_rw [frobSq_conjTranspose]
  rw [hi.2]
  have hgap : (ell:ℝ)-r ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast (show r<ell by omega)))
  field_simp [hgap]

end NLAlib

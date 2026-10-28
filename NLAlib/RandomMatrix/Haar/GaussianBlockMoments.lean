import NLAlib.RandomMatrix.Haar.GaussianInverseContraction
import NLAlib.RandomMatrix.Gaussian.Basic.ComplexBlocks
import NLAlib.RandomMatrix.Gaussian.Basic.ComplexTranspose
import NLAlib.RandomMatrix.Gaussian.Invariance.LinearImage

/-!
# Native source Gaussian blocks for Haar inverse moments

Orthogonal top and bottom coordinate frames applied to one actual Gaussian
matrix have independent native Gaussian laws. Adjointing the top block gives
the product measure used by the proved inverse-Wishart contraction. These
source-level statements supply both the exact cross moment and almost-sure
top-Gram invertibility for the Haar normalization transfer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The adjointed top real Gaussian block and the bottom block have the
exact independent product law, including empty blocks. -/
theorem hasLaw_gaussian_adjoint_top_and_bottom_blocks {n ell s r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℝ) (V : Matrix (Fin n) (Fin s) ℝ)
    (hE : HasOrthonormalCols E) (hV : HasOrthonormalCols V) (hEV : Eᴴ*V=0) :
    HasLaw (fun G : Matrix (Fin n) (Fin r) ℝ => ((Eᴴ*G)ᴴ,Vᴴ*G))
      ((gaussianMatrix (Fin r) (Fin ell)).prod (gaussianMatrix (Fin s) (Fin r)))
      (gaussianMatrix (Fin n) (Fin r)) := by
  have hY := hasLaw_gaussianMatrix_block (t := Fin r) E hE
  have hZ := hasLaw_gaussianMatrix_block (t := Fin r) V hV
  have hX : HasLaw (fun G : Matrix (Fin n) (Fin r) ℝ => (Eᴴ*G)ᴴ)
      (gaussianMatrix (Fin r) (Fin ell)) (gaussianMatrix (Fin n) (Fin r)) :=
    (hasLaw_gaussianMatrix_transpose ell r).comp hY
  have hi := (gaussianMatrix_indepFun_block (t := Fin r) E V hE hV hEV).comp
    Matrix.measurable_conjTranspose measurable_id
  exact hi.hasLaw_prod hX hZ

/-- The same source block pair has its exact circular-complex product law.
Adjointing the top block preserves the complete complex Gaussian law. -/
theorem hasLaw_circularComplexGaussian_adjoint_top_and_bottom_blocks {n ell s r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℂ) (V : Matrix (Fin n) (Fin s) ℂ)
    (hE : HasOrthonormalCols E) (hV : HasOrthonormalCols V) (hEV : Eᴴ*V=0) :
    HasLaw (fun G : Matrix (Fin n) (Fin r) ℂ => ((Eᴴ*G)ᴴ,Vᴴ*G))
      ((circularComplexGaussianMatrix (Fin r) (Fin ell)).prod
        (circularComplexGaussianMatrix (Fin s) (Fin r)))
      (circularComplexGaussianMatrix (Fin n) (Fin r)) := by
  have hY := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := Fin r) Eᴴ
    (by rwa [Matrix.conjTranspose_conjTranspose])
  have hZ := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := Fin r) Vᴴ
    (by rwa [Matrix.conjTranspose_conjTranspose])
  have hX : HasLaw (fun G : Matrix (Fin n) (Fin r) ℂ => (Eᴴ*G)ᴴ)
      (circularComplexGaussianMatrix (Fin r) (Fin ell))
      (circularComplexGaussianMatrix (Fin n) (Fin r)) :=
    hasLaw_conjTranspose_circularComplexGaussianMatrix.comp hY
  have hi := (circularComplexGaussianMatrix_indepFun_block (t := Fin r) E V hE hV hEV).comp
    Matrix.measurable_conjTranspose measurable_id
  exact hi.hasLaw_prod hX hZ

open scoped Matrix.Norms.L2Operator in
/-- Exact native real Gaussian top/bottom inverse-block moment with its
integrability. This is the source cross term in the Haar inverse-Gram trace. -/
theorem integrable_and_integral_frobSq_gaussian_top_bottom_inverse {n ell s r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℝ) (V : Matrix (Fin n) (Fin s) ℝ)
    (hE : HasOrthonormalCols E) (hV : HasOrthonormalCols V) (hEV : Eᴴ*V=0)
    (hr : r+2≤ell) :
    Integrable (fun G : Matrix (Fin n) (Fin r) ℝ => frobSq ((Vᴴ*G)*(pinvR (Eᴴ*G)ᴴ)ᴴ))
      (gaussianMatrix (Fin n) (Fin r)) ∧
      ∫ G, frobSq ((Vᴴ*G)*(pinvR (Eᴴ*G)ᴴ)ᴴ) ∂gaussianMatrix (Fin n) (Fin r)=
        (s:ℝ)*r/((ell:ℝ)-r-1) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_gaussian_mul_pinvR_adjoint_prod hr (s := s)
  have hG := hasLaw_gaussian_adjoint_top_and_bottom_blocks (r := r) E V hE hV hEV
  have hm : Measurable (fun p : Matrix (Fin r) (Fin ell) ℝ × Matrix (Fin s) (Fin r) ℝ =>
      frobSq (p.2*(pinvR p.1)ᴴ)) := measurable_frobSq.comp
    (measurable_snd.matrix_mul (Matrix.measurable_conjTranspose.comp (measurable_pinvR.comp measurable_fst)))
  constructor
  · rw [← hG.map_eq] at hi
    exact hi.comp_aemeasurable hG.aemeasurable
  · exact (hG.integral_comp hm.aestronglyMeasurable).trans hv

open scoped Matrix.Norms.L2Operator in
/-- Exact native circular-complex Gaussian top/bottom inverse-block moment.
Its denominator is `ell-r`, and its full source integrability is proved. -/
theorem integrable_and_integral_frobSq_circularComplexGaussian_top_bottom_inverse {n ell s r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℂ) (V : Matrix (Fin n) (Fin s) ℂ)
    (hE : HasOrthonormalCols E) (hV : HasOrthonormalCols V) (hEV : Eᴴ*V=0)
    (hr : r+1≤ell) :
    Integrable (fun G : Matrix (Fin n) (Fin r) ℂ => frobSq ((Vᴴ*G)*(pinvR (Eᴴ*G)ᴴ)ᴴ))
      (circularComplexGaussianMatrix (Fin n) (Fin r)) ∧
      ∫ G, frobSq ((Vᴴ*G)*(pinvR (Eᴴ*G)ᴴ)ᴴ) ∂circularComplexGaussianMatrix (Fin n) (Fin r)=
        (s:ℝ)*r/((ell:ℝ)-r) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_complexGaussian_mul_pinvR_adjoint_prod hr (s := s)
  have hG := hasLaw_circularComplexGaussian_adjoint_top_and_bottom_blocks (r := r) E V hE hV hEV
  have hm : Measurable (fun p : Matrix (Fin r) (Fin ell) ℂ × Matrix (Fin s) (Fin r) ℂ =>
      frobSq (p.2*(pinvR p.1)ᴴ)) := measurable_frobSq.comp
    (measurable_snd.matrix_mul (Matrix.measurable_conjTranspose.comp (measurable_pinvR.comp measurable_fst)))
  constructor
  · rw [← hG.map_eq] at hi
    exact hi.comp_aemeasurable hG.aemeasurable
  · exact (hG.integral_comp hm.aestronglyMeasurable).trans hv

/-- The native real source Gaussian top block has invertible column Gram
almost surely as soon as its height is at least its width. -/
theorem ae_gaussian_topGram_isUnit {n ell r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℝ) (hE : HasOrthonormalCols E) (hr : r≤ell) :
    ∀ᵐ G ∂gaussianMatrix (Fin n) (Fin r), IsUnit ((Eᴴ*G)ᴴ*(Eᴴ*G)) := by
  have hY := hasLaw_gaussianMatrix_block (t := Fin r) E hE
  have h : ∀ᵐ Y ∂gaussianMatrix (Fin ell) (Fin r), IsUnit (Yᴴ*Y) :=
    gaussianMatrix_ae_isUnit_transpose_mul hr
  rw [← hY.map_eq] at h
  exact ae_of_ae_map hY.aemeasurable h

/-- The native circular-complex source Gaussian top block has invertible
column Gram almost surely, including empty column spaces. -/
theorem ae_circularComplexGaussian_topGram_isUnit {n ell r : ℕ}
    (E : Matrix (Fin n) (Fin ell) ℂ) (hE : HasOrthonormalCols E) (hr : r≤ell) :
    ∀ᵐ G ∂circularComplexGaussianMatrix (Fin n) (Fin r), IsUnit ((Eᴴ*G)ᴴ*(Eᴴ*G)) := by
  have hY := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := Fin r) Eᴴ
    (by rwa [Matrix.conjTranspose_conjTranspose])
  have hX := hasLaw_conjTranspose_circularComplexGaussianMatrix.comp hY
  have h := ae_isUnit_mul_conjTranspose_of_hasLaw_circularComplexGaussianMatrix hX hr
  simpa only [Function.comp_apply,Matrix.conjTranspose_conjTranspose] using h

end NLAlib

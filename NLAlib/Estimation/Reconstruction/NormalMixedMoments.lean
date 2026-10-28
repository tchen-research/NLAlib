import NLAlib.Estimation.Reconstruction.NormalSpectralLaw
import NLAlib.Polynomial.FunctionApproximation.ChebyshevTensor
import NLAlib.Polynomial.FunctionApproximation.ChebyshevPolynomial
import NLAlib.Matrix.Functions.PolynomialVectors
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart

/-!
# Mixed polynomial moments of a normal matrix

The commuting native Hermitian real and imaginary parts encode the two spectral
coordinates. The integral is a cross inner product of two polynomial vectors.
Source: MMSUW 2026, Section 2.1, Lemma 2.1 and equation (2.5).
-/

noncomputable section
open scoped Matrix
open MeasureTheory Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every mixed polynomial moment is the cross inner product of the actual
polynomial vectors for the Hermitian real and imaginary parts.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem integral_normalSpectralLaw_star_poly_re_mul_poly_im
    {A : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (p q : ℂ[X]) :
    (∫ z, star (p.eval (z.re : ℂ)) * q.eval (z.im : ℂ) ∂normalSpectralLaw hA b) =
      star ((aeval (realPart A : Matrix n n ℂ) p) *ᵥ b) ⬝ᵥ
        ((aeval (imaginaryPart A : Matrix n n ℂ) q) *ᵥ b) := by
  have hnormal : IsStarNormal A := ⟨hA.symm⟩
  rw [integral_normalSpectralLaw_eq_quadForm_cfc,
    cfc_mul (fun z : ℂ => star (p.eval (z.re : ℂ))) (fun z : ℂ => q.eval (z.im : ℂ)) A
      (by fun_prop) (by fun_prop),
    cfc_star]
  have hp : cfc (fun z : ℂ => p.eval (z.re : ℂ)) A =
      aeval (realPart A : Matrix n n ℂ) p := by
    rw [← cfc_realPart (fun z => p.eval z) A (by fun_prop) hnormal,
      cfc_polynomial p _ (realPart A).property.isStarNormal]
  have hq : cfc (fun z : ℂ => q.eval (z.im : ℂ)) A =
      aeval (imaginaryPart A : Matrix n n ℂ) q := by
    rw [← cfc_imaginaryPart (fun z => q.eval z) A (by fun_prop) hnormal,
      cfc_polynomial q _ (imaginaryPart A).property.isStarNormal]
  rw [hp, hq]
  rw [quadForm, Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

open scoped Matrix.Norms.L2Operator in
/-- The entire rectangular array of normalized mixed moments is the literal
cross-Gram matrix of the real- and imaginary-part polynomial vectors.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem integral_normalSpectralLaw_normalizedChebyshev_eq_crossGram
    {A : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (M : ℕ)
    (j k : Fin (M+1)) :
    (∫ z, ((normalizedChebyshev j z.re * normalizedChebyshev k z.im : ℝ) : ℂ)
      ∂normalSpectralLaw hA b) =
      ((normalizedChebyshevVectorMatrix (realPart A : Matrix n n ℂ) b M)ᴴ *
        normalizedChebyshevVectorMatrix (imaginaryPart A : Matrix n n ℂ) b M) j k := by
  have h := integral_normalSpectralLaw_star_poly_re_mul_poly_im hA b
    ((normalizedChebyshevPolynomial j).map Complex.ofRealHom)
    ((normalizedChebyshevPolynomial k).map Complex.ofRealHom)
  simpa only [eval_map_normalizedChebyshevPolynomial, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    normalizedChebyshevVectorMatrix, Pi.star_apply] using h

end NLAlib

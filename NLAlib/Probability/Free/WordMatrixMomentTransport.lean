import NLAlib.ForMathlib.Analysis.CStarAlgebra.MatrixFreeAlgebraEvaluation
import NLAlib.ForMathlib.Analysis.CStarAlgebra.MatrixPositiveFunctional
import NLAlib.ForMathlib.MeasureTheory.CStarSpectralLaw
import NLAlib.Probability.Free.WordMomentTransport
import NLAlib.Probability.Free.WordMatrixClosedAlgebra
import NLAlib.Probability.Free.WordMatrixPolynomialL2

/-!
# Genuine amplified semicircular moments, spectra and norms

Actual freeness and individual Catalan laws identify every native
matrix-polynomial expectation and all its powers. Genuine positive diagonal
amplification is faithful when the original state is faithful. Faithfulness
of the actual word vacuum is used only on its proved closed field algebra.
Thus the actual self-adjoint spectra and norms agree, with no supplied joint
law, model-isomorphism or spectrum-identification premise.
This transports the free model used by atlas gaussian-free-spectrum-two-sided;
the quantitative Gaussian comparison is a separate result.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder
namespace NLAlib
variable {D ι A : Type*} [Fintype D] [DecidableEq D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

/-- Generic actual matrix evaluation specializes exactly to the existing native matrix word-polynomial evaluation. -/
@[simp] theorem freeAlgebraEvaluation_wordField
    (P : Matrix D D (FreeAlgebra ℂ ι)) :
    CStarMatrix.freeAlgebraEvaluation ℂ (wordField : ι → B) P=wordMatrixPolynomialEvaluation P := rfl

/-- The genuine amplified expectation of a normalized free semicircular family equals the actual native word-matrix vacuum expectation. -/
theorem normalizedPositiveFunctional_freeAlgebraEvaluation_eq_wordMatrix
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) (X : ι → A)
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (P : Matrix D D (FreeAlgebra ℂ ι)) :
    CStarMatrix.normalizedPositiveFunctional φ (CStarMatrix.freeAlgebraEvaluation ℂ X P)=
      wordMatrixVacuumExpectation (wordMatrixPolynomialEvaluation P) := by
  change (Fintype.card D : ℂ)⁻¹*(∑ j,φ (FreeAlgebra.lift ℂ X (P j j)))=
    (Fintype.card D : ℂ)⁻¹*(∑ j,wordVacuumExpectation ι (FreeAlgebra.lift ℂ wordField (P j j)))
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    freeAlgebra_lift_moment_eq_wordField_of_semicircular φ.toLinearMap hφ X hFree hLaw (P j j)

/-- All actual amplified matrix-polynomial power moments agree with the corresponding genuine native word-model moments. -/
theorem normalizedPositiveFunctional_freeAlgebraEvaluation_pow_eq_wordMatrix
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) (X : ι → A)
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (P : Matrix D D (FreeAlgebra ℂ ι)) (n : ℕ) :
    CStarMatrix.normalizedPositiveFunctional φ ((CStarMatrix.freeAlgebraEvaluation ℂ X P)^n)=
      wordMatrixVacuumExpectation ((wordMatrixPolynomialEvaluation P)^n) := by
  have hh := normalizedPositiveFunctional_freeAlgebraEvaluation_eq_wordMatrix φ hφ X hFree hLaw (P^n)
  change CStarMatrix.normalizedPositiveFunctional φ (CStarMatrix.freeAlgebraEvaluation ℂ X (P^n))=
    wordMatrixVacuumExpectation (CStarMatrix.freeAlgebraEvaluation ℂ (wordField : ι → B) (P^n)) at hh
  simpa only [map_pow,freeAlgebraEvaluation_wordField] using hh

/-- A faithful positive free semicircular model has the same actual real spectrum as its native word-matrix polynomial whenever the two evaluated polynomials are self-adjoint. No spectral transport certificate is assumed.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem spectrum_freeAlgebraEvaluation_eq_wordMatrix_of_semicircular
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hfaithful : ∀ a : A, φ (star a*a)=0 → a=0) (X : ι → A)
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (P : Matrix D D (FreeAlgebra ℂ ι))
    (hPX : IsSelfAdjoint (CStarMatrix.freeAlgebraEvaluation ℂ X P))
    (hPW : IsSelfAdjoint (wordMatrixPolynomialEvaluation P)) :
    spectrum ℝ (CStarMatrix.freeAlgebraEvaluation ℂ X P)=
      spectrum ℝ (wordMatrixPolynomialEvaluation P) := by
  apply spectrum_real_eq_of_faithful_power_moments
    (CStarMatrix.normalizedPositiveFunctional φ) (wordMatrixVacuumPositiveMap (D := D) (ι := ι))
    ⊤ isClosed_univ (wordMatrixFieldAlgebra (D := D) (ι := ι)) isClosed_wordMatrixFieldAlgebra
  · intro T _ hz
    exact CStarMatrix.eq_zero_of_normalizedPositiveFunctional_star_mul_eq_zero φ hfaithful T hz
  · intro T hT hz
    exact eq_zero_of_entries_mem_wordFieldAlgebra_of_wordMatrixVacuumExpectation_star_mul_eq_zero T hT hz
  · exact hPX
  · exact hPW
  · trivial
  · intro i j
    exact freeAlgebra_lift_wordField_mem_wordFieldAlgebra (P i j)
  · intro n
    exact congrArg Complex.re
      (normalizedPositiveFunctional_freeAlgebraEvaluation_pow_eq_wordMatrix φ hφ X hFree hLaw P n)

/-- Actual self-adjoint matrix-polynomial operator norms agree between a faithful free semicircular model and the concrete word model. -/
theorem norm_freeAlgebraEvaluation_eq_wordMatrix_of_semicircular
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hfaithful : ∀ a : A, φ (star a*a)=0 → a=0) (X : ι → A)
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (P : Matrix D D (FreeAlgebra ℂ ι))
    (hPX : IsSelfAdjoint (CStarMatrix.freeAlgebraEvaluation ℂ X P))
    (hPW : IsSelfAdjoint (wordMatrixPolynomialEvaluation P)) :
    ‖CStarMatrix.freeAlgebraEvaluation ℂ X P‖=‖wordMatrixPolynomialEvaluation P‖ := by
  have hs := spectrum_freeAlgebraEvaluation_eq_wordMatrix_of_semicircular φ hφ hfaithful X hFree hLaw P hPX hPW
  rw [← hPX.toReal_spectralRadius_eq_norm,← hPW.toReal_spectralRadius_eq_norm]
  simp only [spectralRadius,hs]

end NLAlib

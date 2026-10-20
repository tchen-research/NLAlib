import NLAlib.Probability.Free.WordMatrixMomentTransport
import NLAlib.Probability.Free.WordNativeMatrixLinearCombination

/-!
# Faithful semicircular transport for the actual affine matrix model

The entrywise matrix polynomial evaluation is exactly the existing native
word-field affine model. Actual self-adjointness, freeness, individual
Catalan laws and a faithful positive state therefore identify the genuine
spectra and norms, without a supplied joint-law or spectrum certificate.
These are model-transport prerequisites for atlas gaussian-free-spectrum-two-sided.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder
namespace NLAlib
variable {D ι A : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι
local notation "M" => CStarMatrix D D B

/-- The native word-field linear combination is the actual entrywise affine matrix evaluation. -/
theorem wordNativeMatrixLinearCombination_eq_affineCombination
    (A₀ : Matrix D D ℂ) (C : ι → Matrix D D ℂ) :
    wordNativeMatrixLinearCombination A₀ C=CStarMatrix.affineCombination ℂ A₀ C wordField := by
  apply CStarMatrix.ext
  intro i j
  let E : M →ₗ[ℂ] B :=
    { toFun := fun T => T i j
      map_add' T U := CStarMatrix.add_apply T U i j
      map_smul' c T := CStarMatrix.smul_apply c T i j }
  let F : ι → M := fun k => CStarMatrix.ofMatrix (fun i j => C k i j•wordField k)
  have hs : (∑ k,F k) i j=∑ k,C k i j•wordField k := by
    exact map_sum E F Finset.univ
  unfold wordNativeMatrixLinearCombination
  rw [CStarMatrix.add_apply]
  change (A₀ i j)•(1 : B)+(∑ k,F k) i j=algebraMap ℂ B (A₀ i j)+∑ k,C k i j•wordField k
  rw [hs,Algebra.algebraMap_eq_smul_one]

/-- The actual matrix linear polynomial evaluates to the native word-field affine model. -/
theorem wordMatrixPolynomialEvaluation_matrixLinearPolynomial
    (A₀ : Matrix D D ℂ) (C : ι → Matrix D D ℂ) :
    wordMatrixPolynomialEvaluation (FreeAlgebra.matrixLinearPolynomial A₀ C)=
      wordNativeMatrixLinearCombination A₀ C := by
  rw [← freeAlgebraEvaluation_wordField,CStarMatrix.freeAlgebraEvaluation_matrixLinearPolynomial,
    wordNativeMatrixLinearCombination_eq_affineCombination]

/-- Actual Hermitian affine combinations in any faithful positive free semicircular model have the native word-model spectrum. Source: Bandeira–Boedihardjo–van Handel, Theorem 6.2 endpoint model;
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem spectrum_affineCombination_eq_wordNativeMatrixLinearCombination
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hfaithful : ∀ a : A, φ (star a*a)=0 → a=0) (X : ι → A)
    (hX : ∀ i, IsSelfAdjoint (X i))
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (A₀ : Matrix D D ℂ) (hA₀ : A₀.IsHermitian) (C : ι → Matrix D D ℂ)
    (hC : ∀ i, (C i).IsHermitian) :
    spectrum ℝ (CStarMatrix.affineCombination ℂ A₀ C X)=
      spectrum ℝ (wordNativeMatrixLinearCombination A₀ C) := by
  have hh := spectrum_freeAlgebraEvaluation_eq_wordMatrix_of_semicircular φ hφ hfaithful X hFree hLaw
    (FreeAlgebra.matrixLinearPolynomial A₀ C)
    (by rw [CStarMatrix.freeAlgebraEvaluation_matrixLinearPolynomial]
        exact CStarMatrix.isSelfAdjoint_affineCombination A₀ hA₀ C hC X hX)
    (by rw [wordMatrixPolynomialEvaluation_matrixLinearPolynomial]
        exact isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hC)
  simpa only [CStarMatrix.freeAlgebraEvaluation_matrixLinearPolynomial,
    wordMatrixPolynomialEvaluation_matrixLinearPolynomial] using hh

/-- Actual Hermitian affine combinations in a faithful positive free semicircular model have the native word-model norm. -/
theorem norm_affineCombination_eq_wordNativeMatrixLinearCombination
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hfaithful : ∀ a : A, φ (star a*a)=0 → a=0) (X : ι → A)
    (hX : ∀ i, IsSelfAdjoint (X i))
    (hFree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (A₀ : Matrix D D ℂ) (hA₀ : A₀.IsHermitian) (C : ι → Matrix D D ℂ)
    (hC : ∀ i, (C i).IsHermitian) :
    ‖CStarMatrix.affineCombination ℂ A₀ C X‖=‖wordNativeMatrixLinearCombination A₀ C‖ := by
  have hs := spectrum_affineCombination_eq_wordNativeMatrixLinearCombination φ hφ hfaithful X hX hFree hLaw A₀ hA₀ C hC
  have hleft := CStarMatrix.isSelfAdjoint_affineCombination A₀ hA₀ C hC X hX
  have hright := isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hC
  rw [← hleft.toReal_spectralRadius_eq_norm,← hright.toReal_spectralRadius_eq_norm]
  simp only [spectralRadius,hs]

end NLAlib

import NLAlib.ForMathlib.Probability.FreeMoments
import NLAlib.Probability.Free.WordPolynomialFreeness
import NLAlib.Probability.Free.WordCatalanMoments
import NLAlib.Probability.Free.WordVacuumSeparation

/-!
# Genuine joint moments transport to the concrete semicircular word model

The actual word fields satisfy polynomial freeness. Standard Catalan moments
and the algebraic uniqueness theorem then identify every joint free-algebra
polynomial expectation of any normalized free semicircular family. No joint
law equality or concrete representation premise is supplied. Spectral
transport through faithfulness is a separate analytic step.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib
variable {ι A : Type*} [Ring A] [Algebra ℂ A]

/-- The concrete fields satisfy the usual polynomial definition of freeness. -/
theorem isFreeFamily_wordField :
    NoncommutativeProbability.IsFreeFamily
      (wordVacuumExpectation ι).toLinearMap (wordField : ι → (WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι)) := by
  intro m hm color hcolor P hP
  exact wordVacuumExpectation_ofFn_prod_aeval_eq_zero hm color hcolor P hP

/-- Standard semicircular power moments give the genuine concrete field moment for every one-variable polynomial. -/
theorem aeval_moment_eq_wordField_of_semicircular
    (φ : A →ₗ[ℂ] ℂ) (X : ι → A)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (i : ι) (P : Polynomial ℂ) :
    φ (Polynomial.aeval (X i) P)=wordVacuumExpectation ι (Polynomial.aeval (wordField i) P) := by
  apply NoncommutativeProbability.aeval_moment_eq_of_powers
  intro n
  exact (hLaw i n).trans (wordVacuumExpectation_wordField_pow_eq i n).symm

/-- Genuine freeness and the standard single-variable semicircular laws determine the actual joint polynomial expectation in the concrete free model. No equality of joint laws is assumed.
This is the algebraic transport prerequisite for atlas gaussian-free-spectrum-two-sided. -/
theorem freeAlgebra_lift_moment_eq_wordField_of_semicircular
    (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1=1) (X : ι → A)
    (hFree : NoncommutativeProbability.IsFreeFamily φ X)
    (hLaw : ∀ (i : ι) (n : ℕ), φ (X i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (P : FreeAlgebra ℂ ι) :
    φ (FreeAlgebra.lift ℂ X P)=wordVacuumExpectation ι (FreeAlgebra.lift ℂ wordField P) := by
  exact NoncommutativeProbability.freeAlgebra_lift_moment_eq_of_free φ
    (wordVacuumExpectation ι).toLinearMap X wordField hφ wordVacuumExpectation_one
    hFree isFreeFamily_wordField (aeval_moment_eq_wordField_of_semicircular φ X hLaw) P

/-- Every genuine native free-algebra polynomial in the actual fields belongs to their actual closed star algebra. -/
theorem freeAlgebra_lift_wordField_mem_wordFieldAlgebra (P : FreeAlgebra ℂ ι) :
    FreeAlgebra.lift ℂ (wordField : ι → (WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι)) P∈wordFieldAlgebra ι := by
  induction P using FreeAlgebra.induction with
  | grade0 c => simpa only [AlgHom.commutes] using (wordFieldAlgebra ι).algebraMap_mem c
  | grade1 i =>
    simp only [FreeAlgebra.lift_ι_apply]
    exact StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))
  | mul P Q hP hQ => simpa only [map_mul] using mul_mem hP hQ
  | add P Q hP hQ => simpa only [map_add] using add_mem hP hQ

end NLAlib

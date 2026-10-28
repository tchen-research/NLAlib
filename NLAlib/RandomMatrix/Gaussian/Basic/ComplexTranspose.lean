import NLAlib.RandomMatrix.Gaussian.Basic.ComplexGaussianMatrix
import NLAlib.RandomMatrix.Gaussian.Invariance.Invariance
import NLAlib.Probability.Gaussian.Basic.ComplexConjugation

/-!
# Transpose and adjoint laws of native complex Gaussian matrices

Coordinate permutation and conjugation preserve the complete circular complex
matrix product law, including independence and empty dimensions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n]

private theorem circularMatrix_eq_map_curry :
    circularComplexGaussianMatrix m n = (circularComplexGaussianVector (m × n)).map
      ((MeasurableEquiv.curry m n ℂ).trans Matrix.ofMeasurableEquiv) :=
  (hasLaw_curry_circularComplexGaussianVector (m := m) (n := n)).map_eq.symm

/-- Transposition preserves the full native circular complex Gaussian law. -/
theorem hasLaw_transpose_circularComplexGaussianMatrix :
    HasLaw (fun G : Matrix m n ℂ => Gᵀ) (circularComplexGaussianMatrix n m)
      (circularComplexGaussianMatrix m n) := by
  refine ⟨Matrix.measurable_transpose.aemeasurable,?_⟩
  rw [circularMatrix_eq_map_curry,
    Measure.map_map Matrix.measurable_transpose (MeasurableEquiv.measurable _)]
  have hfun : (fun G : Matrix m n ℂ => Gᵀ) ∘
      ((MeasurableEquiv.curry m n ℂ).trans Matrix.ofMeasurableEquiv) =
      ((MeasurableEquiv.curry n m ℂ).trans Matrix.ofMeasurableEquiv) ∘
        (fun x : m × n → ℂ => fun ji : n × m => x ji.swap) := by
    funext x
    rfl
  have hswap : Measurable (fun x : m × n → ℂ => fun ji : n × m => x ji.swap) :=
    measurable_pi_lambda _ fun ji => measurable_pi_apply _
  rw [hfun,← Measure.map_map (MeasurableEquiv.measurable _) hswap,
    map_comp_injective_pi _ Prod.swap Prod.swap_injective,← circularMatrix_eq_map_curry]

/-- Natural-dimension spelling of the full transpose law. -/
theorem hasLaw_circularComplexGaussianMatrix_transpose (m n : ℕ) :
    HasLaw (fun G : Matrix (Fin m) (Fin n) ℂ => Gᵀ)
      (circularComplexGaussianMatrix (Fin n) (Fin m))
      (circularComplexGaussianMatrix (Fin m) (Fin n)) := hasLaw_transpose_circularComplexGaussianMatrix

/-- Entrywise conjugation preserves the actual native complex matrix law. -/
theorem hasLaw_conj_circularComplexGaussianMatrix :
    HasLaw (fun G : Matrix m n ℂ => G.map star) (circularComplexGaussianMatrix m n)
      (circularComplexGaussianMatrix m n) := by
  have hs : MeasurePreserving (star : (n → ℂ) → n → ℂ)
      (circularComplexGaussianVector n) (circularComplexGaussianVector n) :=
    ⟨(by fun_prop),hasLaw_star_circularComplexGaussianVector.map_eq⟩
  have hp := measurePreserving_pi (fun _ : m => circularComplexGaussianVector n)
    (fun _ : m => circularComplexGaussianVector n) (fun _ => hs)
  have hm := measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix (m := m) (n := n)
  exact (hm.comp (hp.comp hm.symm)).hasLaw

/-- Conjugate transposition preserves the actual circular complex Gaussian
matrix product law, reversing the rectangular dimensions. -/
theorem hasLaw_conjTranspose_circularComplexGaussianMatrix :
    HasLaw (fun G : Matrix m n ℂ => Gᴴ) (circularComplexGaussianMatrix n m)
      (circularComplexGaussianMatrix m n) := by
  exact hasLaw_transpose_circularComplexGaussianMatrix.comp hasLaw_conj_circularComplexGaussianMatrix

end NLAlib

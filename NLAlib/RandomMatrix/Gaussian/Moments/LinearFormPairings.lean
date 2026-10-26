import NLAlib.RandomMatrix.Gaussian.Basic.LinearForms
import NLAlib.Probability.Gaussian.Moments.Isserlis

/-!
# Wick pairing formula for Gaussian matrix linear forms

Any finite family of real linear forms of the genuine Gaussian matrix has
the exact Wick expansion, with covariance given by the coefficient inner
products. The accompanying product integrability justifies finite trace
expansions for ensembles built from linear combinations of matrix entries.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

private def matrixLinearFormVector {r s k : ℕ} (a : Fin k → Fin r → Fin s → ℝ) :
    Matrix (Fin r) (Fin s) ℝ →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap.comp (linFormCLM a)

private theorem hasGaussianLaw_matrixLinearFormVector {r s k : ℕ}
    (a : Fin k → Fin r → Fin s → ℝ) :
    HasGaussianLaw (matrixLinearFormVector a) (gaussianMatrix (Fin r) (Fin s)) :=
  (hasGaussianLaw_id_gaussianMatrix _ _).map_of_measurable
    (matrixLinearFormVector a) (matrixLinearFormVector a).continuous.measurable

private theorem integral_matrixLinearFormVector {r s k : ℕ}
    (a : Fin k → Fin r → Fin s → ℝ) :
    (∫ G, matrixLinearFormVector a G ∂gaussianMatrix (Fin r) (Fin s)) = 0 := by
  rw [WithLp.ext_iff]
  funext i
  have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).integral_comp_comm
    (hasGaussianLaw_matrixLinearFormVector a).integrable
  change (∫ G, matrixLinearFormVector a G ∂gaussianMatrix (Fin r) (Fin s)) i = 0
  exact h.symm.trans (integral_linForm_gaussianMatrix (a i))

/-- A finite product of Gaussian matrix linear forms is integrable, with no
independence or nonsingularity requirement on the chosen coefficient arrays. -/
theorem integrable_prod_linForm_gaussianMatrix {r s k : ℕ}
    (a : Fin k → Fin r → Fin s → ℝ) :
    Integrable (fun G => ∏ i, linForm (a i) G) (gaussianMatrix (Fin r) (Fin s)) :=
  integrable_prod_gaussianVector_of_centered (matrixLinearFormVector a)
    (hasGaussianLaw_matrixLinearFormVector a) (integral_matrixLinearFormVector a) (fun i => i)

/-- Gaussian matrix linear forms have the exact Wick pairing formula; the
pair covariance is the ordinary inner product of their coefficient arrays.
Source: Isserlis 1918; Janson 1997, Theorem 1.28. -/
theorem integral_prod_linForm_gaussianMatrix_eq_sum_pairings {r s k : ℕ}
    (a : Fin k → Fin r → Fin s → ℝ) :
    (∫ G, ∏ i, linForm (a i) G ∂gaussianMatrix (Fin r) (Fin s)) =
      ∑ π : GaussianPairings k,
        gaussianPairingWeight (fun i j => ∑ u, ∑ v, a i u v * a j u v) π := by
  have h := integral_prod_gaussianVector_eq_sum_pairings
    (matrixLinearFormVector a) (hasGaussianLaw_matrixLinearFormVector a)
    (integral_matrixLinearFormVector a) (fun i => i)
  simpa only [show ∀ G i, matrixLinearFormVector a G i = linForm (a i) G from fun _ _ => rfl,
    integral_linForm_mul_two_gaussianMatrix] using h

end NLAlib

import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Polynomial densities and actual modified measures

A polynomial density that is nonnegative almost everywhere defines an actual
positive measure. Its moment functional is the existing polynomial-weighted
functional, so endpoint modified moment statements have native measure consumers.
-/

noncomputable section
open Polynomial MeasureTheory

namespace NLAlib

/-- A nonnegative polynomial density preserves all finite polynomial moments. -/
theorem hasPolynomialMoments_withDensity_polynomial {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (w : ℝ[X]) (hw : ∀ᵐ x ∂μ, 0 ≤ w.eval x) :
    HasPolynomialMoments (μ.withDensity (fun x => ENNReal.ofReal (w.eval x))) := by
  intro p
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)).mpr
  apply (hμ (w * p)).congr
  filter_upwards [hw] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, eval_mul]

/-- The native nonnegative polynomial-density measure has exactly the existing
polynomial-weighted integral functional.
atlas: gauss-radau-lobatto (partial) -/
theorem polynomialIntegral_withDensity_polynomial {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (w : ℝ[X]) (hw : ∀ᵐ x ∂μ, 0 ≤ w.eval x) :
    polynomialIntegral (μ.withDensity (fun x => ENNReal.ofReal (w.eval x)))
      (hasPolynomialMoments_withDensity_polynomial hμ w hw) =
        polynomialWeightedFunctional (polynomialIntegral μ hμ) w := by
  apply LinearMap.ext
  intro p
  rw [polynomialIntegral_apply, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with x; exact ENNReal.ofReal_lt_top),
    polynomialWeightedFunctional_apply, polynomialIntegral_apply]
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, eval_mul]

end NLAlib

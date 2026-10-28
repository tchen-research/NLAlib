import NLAlib.Probability.Gaussian.Basic.CircularComplex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact Laplace transforms of squared complex Gaussian moduli

The circular convention has two independent variance-one real coordinates.
Its squared modulus therefore has transform `(1-2t)⁻¹` on `t<1/2`.
These are direct Gaussian integrals, including all negative transform parameters.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace NLAlib

private theorem gaussianPDFReal_mul_exp_sq (t x : ℝ) :
    gaussianPDFReal 0 1 x * exp (t * x ^ 2) =
      (sqrt (2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

/-- The exact quadratic exponential is integrable throughout its natural domain. -/
theorem integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
  simp_rw [smul_eq_mul, toReal_gaussianPDF, gaussianPDFReal_mul_exp_sq]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1 / 2 - t)).const_mul _

/-- Squaring the real quadratic Laplace transform removes all square roots. -/
theorem integral_exp_mul_sq_gaussianReal_sq {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, exp (t * x ^ 2) ∂gaussianReal 0 1) ^ 2 = (1 - 2 * t)⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp_rw [smul_eq_mul, gaussianPDFReal_mul_exp_sq]
  rw [integral_const_mul, integral_gaussian, mul_pow, inv_pow,
    sq_sqrt (by positivity : 0 ≤ 2 * π),
    sq_sqrt (div_nonneg pi_pos.le (by linarith : 0 ≤ 1 / 2 - t))]
  field_simp

private theorem exp_normSq_mk (t x y : ℝ) :
    exp (t * Complex.normSq (⟨x, y⟩ : ℂ)) = exp (t * x ^ 2) * exp (t * y ^ 2) := by
  rw [← exp_add]
  congr 1
  change t * (x * x + y * y) = _
  ring

/-- Squared-modulus exponential moments are integrable for the actual complex law. -/
theorem integrable_exp_mul_normSq_circularComplexGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℂ => exp (t * Complex.normSq z)) circularComplexGaussian := by
  unfold circularComplexGaussian
  have hm : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.measurable
  apply (integrable_map_measure (by fun_prop) hm.aemeasurable).mpr
  simpa only [Function.comp_def, exp_normSq_mk] using
    (integrable_exp_mul_sq_gaussianReal ht).mul_prod (integrable_exp_mul_sq_gaussianReal ht)

/-- The exact squared-modulus Laplace transform of the circular complex Gaussian. -/
theorem integral_exp_mul_normSq_circularComplexGaussian {t : ℝ} (ht : t < 1 / 2) :
    ∫ z : ℂ, exp (t * Complex.normSq z) ∂circularComplexGaussian = (1 - 2 * t)⁻¹ := by
  have hm : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.measurable
  rw [circularComplexGaussian, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [exp_normSq_mk]
  rw [integral_prod_mul (fun x : ℝ => exp (t * x ^ 2)) (fun x : ℝ => exp (t * x ^ 2)), ← pow_two]
  exact integral_exp_mul_sq_gaussianReal_sq ht

/-- A finite diagonal quadratic exponential is integrable on its exact product-law domain. -/
theorem integrable_exp_sum_mul_normSq_circularComplexGaussianVector
    {n : Type*} [Fintype n] (t : n → ℝ) (ht : ∀ i, t i < 1 / 2) :
    Integrable (fun z : n → ℂ => exp (∑ i, t i * Complex.normSq (z i)))
      (circularComplexGaussianVector n) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_normSq_circularComplexGaussian (ht i))

/-- Exact finite-product Laplace transform, with arbitrary signed diagonal coefficients. -/
theorem integral_exp_sum_mul_normSq_circularComplexGaussianVector
    {n : Type*} [Fintype n] (t : n → ℝ) (ht : ∀ i, t i < 1 / 2) :
    ∫ z : n → ℂ, exp (∑ i, t i * Complex.normSq (z i)) ∂circularComplexGaussianVector n =
      ∏ i, (1 - 2 * t i)⁻¹ := by
  simp_rw [exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (z : ℂ) => exp (t i * Complex.normSq z))]
  exact Finset.prod_congr rfl fun i _ => integral_exp_mul_normSq_circularComplexGaussian (ht i)

end NLAlib

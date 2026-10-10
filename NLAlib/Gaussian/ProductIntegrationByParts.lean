import NLAlib.Gaussian.PolynomialGrowthIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gaussian coordinate integration by parts with moderate growth

This is the finite-dimensional Stein identity for C1 functions whose values
and partial derivatives have polynomial growth. Gaussian moments supply all
integrability premises. The proof applies the one-dimensional adjoint identity
to coordinate sections, then uses the product resampling operator.

Source: Vershynin 2018, Lemma 7.2.3. Atlas: `gaussian-integration-by-parts`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib
variable {ι : Type*} [Fintype ι]

/-- Finite-dimensional Gaussian polynomial majorants are integrable.
Source: Gaussian moments; atlas `gaussian-integration-by-parts`. -/
theorem integrable_one_add_norm_pow_pi_gaussianReal (d : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ d)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hX : MemLp (fun x : ι → ℝ => x) (d : ENNReal)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (hasGaussianLaw_id_pi_gaussianReal ι).memLp (by simp)
  have h := ((memLp_const (1 : ℝ)).add hX.norm).integrable_norm_pow'
  simp only [Pi.add_apply, Real.norm_eq_abs] at h
  convert h using 1
  funext x
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 + ‖x‖)]

/-- Polynomial growth provides integrability under any finite standard
Gaussian product. Source: Gaussian moments; atlas `gaussian-integration-by-parts`. -/
theorem integrable_pi_gaussianReal_of_polynomial_growth
    {f : (ι → ℝ) → ℝ}
    (hf : AEMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (C : ℝ) (d : ℕ) (hBound : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_one_add_norm_pow_pi_gaussianReal d).const_mul C)
    hf.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hBound x

/-- Polynomial-growth scalar functions on Gaussian space have finite second
moments. Source: Gaussian moments; atlas `gaussian-integration-by-parts`. -/
theorem memLp_two_pi_gaussianReal_of_polynomial_growth
    {f : (ι → ℝ) → ℝ}
    (hf : AEMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (C : ℝ) (d : ℕ) (hBound : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  refine Integrable.mono'
    ((integrable_one_add_norm_pow_pi_gaussianReal (d * 2)).const_mul (C ^ 2))
    (hf.pow_const 2).aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  have h := pow_le_pow_left₀ (abs_nonneg (f x)) (hBound x) 2
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs, mul_pow, pow_mul] using h

variable [DecidableEq ι]

/-- A coordinate section derivative is the corresponding Frechet derivative
evaluation. Source: coordinate calculus; atlas `gaussian-integration-by-parts`. -/
theorem deriv_update_eq_fderiv_single {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (x : ι → ℝ) (i : ι) (t : ℝ) :
    deriv (fun u => f (Function.update x i u)) t =
      fderiv ℝ f (Function.update x i t) (Pi.single i 1) :=
  (((hf.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update x i t)).deriv

private theorem norm_update_le (x : ι → ℝ) (i : ι) (t : ℝ) :
    ‖Function.update x i t‖ ≤ ‖x‖ + |t| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  by_cases hji : j = i
  · subst j
    simp [Function.update, Real.norm_eq_abs]
  · simpa [Function.update, hji] using
      (norm_le_pi_norm x j).trans (le_add_of_nonneg_right (abs_nonneg t))

private theorem section_growth {f : (ι → ℝ) → ℝ}
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hBound : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) (x : ι → ℝ) (i : ι) :
    ∀ t, |f (Function.update x i t)| ≤
      (C * (1 + ‖x‖) ^ d) * (1 + |t|) ^ d := by
  intro t
  have hN : 1 + ‖Function.update x i t‖ ≤ (1 + ‖x‖) * (1 + |t|) := by
    have h := norm_update_le x i t
    nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg t)]
  calc
    |f (Function.update x i t)| ≤ C * (1 + ‖Function.update x i t‖) ^ d := hBound _
    _ ≤ C * ((1 + ‖x‖) * (1 + |t|)) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hN d) hC
    _ = (C * (1 + ‖x‖) ^ d) * (1 + |t|) ^ d := by rw [mul_pow]; ring

/-- Full finite-dimensional standard-Gaussian Stein identity for C1 functions
of polynomial growth, with polynomial-growth partial derivatives.
All moments and integrability needed for Fubini and the derivative identity
are proved. Source: Vershynin 2018, Lemma 7.2.3;
atlas `gaussian-integration-by-parts`.
atlas: gaussian-integration-by-parts -/
theorem integral_coord_mul_eq_integral_fderiv_pi_gaussianReal
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (d e : ℕ)
    (hValue : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d)
    (hPartial : ∀ i x, |fderiv ℝ f x (Pi.single i 1)| ≤ D * (1 + ‖x‖) ^ e)
    (i : ι) :
    ∫ x, x i * f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ x, fderiv ℝ f x (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let μ : ι → Measure ℝ := fun _ => gaussianReal 0 1
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hD : 0 ≤ D := by
    have h := hPartial i 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hFm : AEMeasurable f (Measure.pi μ) := hf.continuous.measurable.aemeasurable
  have hF2 := memLp_two_pi_gaussianReal_of_polynomial_growth hFm C d hValue
  have hXi : MemLp (fun x : ι → ℝ => x i) 2 (Measure.pi μ) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) (2 : NNReal)).comp_measurePreserving
      (measurePreserving_eval μ i)
  have hLeftInt : Integrable (fun x : ι → ℝ => x i * f x) (Measure.pi μ) :=
    hXi.integrable_mul hF2
  have hDc : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hRightInt := integrable_pi_gaussianReal_of_polynomial_growth
    hDc.measurable.aemeasurable D e (hPartial i)
  rw [← integral_integral_update_pi μ i hLeftInt,
    ← integral_integral_update_pi μ i hRightInt]
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  have hLine : Differentiable ℝ (fun t => f (Function.update x i t)) :=
    fun t => (((hf.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)).differentiableAt
  have hLineDeriv (t : ℝ) :
      |deriv (fun u => f (Function.update x i u)) t| ≤
        (D * (1 + ‖x‖) ^ e) * (1 + |t|) ^ e := by
    rw [deriv_update_eq_fderiv_single hf]
    exact section_growth D hD e (hPartial i) x i t
  have hStein := integral_mul_eq_integral_deriv_gaussianReal_of_polynomial_growth
    (fun t => f (Function.update x i t)) hLine
    (C * (1 + ‖x‖) ^ d) (D * (1 + ‖x‖) ^ e) d e
    (section_growth C hC d hValue x i) hLineDeriv
  simpa only [Function.update_self, deriv_update_eq_fderiv_single hf] using hStein

end NLAlib

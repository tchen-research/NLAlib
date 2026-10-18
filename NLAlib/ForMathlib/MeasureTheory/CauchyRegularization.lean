import NLAlib.ForMathlib.MeasureTheory.CauchyApproximation

/-!
# Weak reconstruction by Cauchy regularization

For a finite measure, the Cauchy regularized density recovers every bounded
continuous test in the zero-scale limit. This provides measure uniqueness
from the imaginary part of its Cauchy transform.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace MeasureTheory

/-- A bounded test times a Cauchy density is integrable. -/
theorem integrable_boundedContinuousFunction_mul_cauchyPDFReal
    (f : ℝ →ᵇ ℝ) (x : ℝ) (γ : NNReal) :
    Integrable (fun y : ℝ => f y * cauchyPDFReal x γ y) :=
  (integrable_cauchyPDFReal x).bdd_mul f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y))

/-- Norm integrals of Cauchy-averaged bounded tests remain bounded by
the test's uniform norm. -/
theorem integral_norm_boundedContinuousFunction_mul_cauchyPDFReal_le
    (f : ℝ →ᵇ ℝ) (x : ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    (∫ y : ℝ, ‖f y * cauchyPDFReal x γ y‖) ≤ ‖f‖ := by
  calc
    _ ≤ ∫ y : ℝ, ‖f‖ * cauchyPDFReal x γ y := by
      apply integral_mono (integrable_boundedContinuousFunction_mul_cauchyPDFReal f x γ).norm
        ((integrable_cauchyPDFReal x).const_mul ‖f‖)
      intro y
      change ‖f y * cauchyPDFReal x γ y‖ ≤ ‖f‖ * cauchyPDFReal x γ y
      rw [norm_mul, Real.norm_of_nonneg (cauchyPDF_pos x hγ y).le]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm y) (cauchyPDF_pos x hγ y).le
    _ = _ := by rw [integral_const_mul, integral_cauchyPDFReal_eq_one x hγ, mul_one]

/-- Fubini applies to Cauchy regularization of every bounded continuous
test under an arbitrary finite source measure. -/
theorem integrable_boundedContinuousFunction_mul_cauchyPDFReal_prod
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →ᵇ ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    Integrable (fun p : ℝ × ℝ => f p.2 * cauchyPDFReal p.1 γ p.2) (μ.prod volume) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => f p.2 * cauchyPDFReal p.1 γ p.2) := by
    have hf : StronglyMeasurable (fun p : ℝ × ℝ => f p.2) :=
      (f.continuous.comp continuous_snd).stronglyMeasurable
    unfold cauchyPDFReal
    exact hf.mul (by fun_prop)
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall
      (fun x => integrable_boundedContinuousFunction_mul_cauchyPDFReal f x γ)
  · apply (integrable_const ‖f‖).mono' (hm.norm.integral_prod_right').aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact integral_norm_boundedContinuousFunction_mul_cauchyPDFReal_le f x γ hγ)

/-- The integral against the regularized density is the integral of
standard-Cauchy affine averages. -/
theorem integral_cauchyRegularization_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ →ᵇ ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    (∫ y : ℝ, f y * (∫ x : ℝ, cauchyPDFReal x γ y ∂μ)) =
      ∫ x : ℝ, ∫ t : ℝ, f (x + γ * t) ∂cauchyMeasure 0 1 ∂μ := by
  calc
    _ = ∫ y : ℝ, ∫ x : ℝ, f y * cauchyPDFReal x γ y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => (integral_const_mul (f y) _).symm)
    _ = ∫ x : ℝ, (∫ y : ℝ, f y * cauchyPDFReal x γ y) ∂μ :=
      (integral_integral_swap
        (integrable_boundedContinuousFunction_mul_cauchyPDFReal_prod μ f γ hγ)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => integral_mul_cauchyPDFReal_eq_integral_affine f x γ hγ)

/-- Cauchy density regularization recovers each bounded continuous
integral as its positive scale tends to zero. -/
theorem tendsto_integral_cauchyRegularization (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ →ᵇ ℝ) {γ : ℕ → NNReal} (hγne : ∀ n, γ n ≠ 0)
    (hγ : Tendsto (fun n => (γ n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y : ℝ, f y * (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂μ))
      atTop (𝓝 (∫ x : ℝ, f x ∂μ)) := by
  have hm (n : ℕ) : StronglyMeasurable
      (fun p : ℝ × ℝ => f (p.1 + γ n * p.2)) :=
    (f.continuous.comp (by fun_prop)).stronglyMeasurable
  have hbound (n : ℕ) (x : ℝ) :
      ‖∫ t : ℝ, f (x + γ n * t) ∂cauchyMeasure 0 1‖ ≤ ‖f‖ := by
    calc
      _ ≤ ∫ t : ℝ, ‖f (x + γ n * t)‖ ∂cauchyMeasure 0 1 := norm_integral_le_integral_norm _
      _ ≤ ∫ _t : ℝ, ‖f‖ ∂cauchyMeasure 0 1 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (integrable_const _)
        exact Filter.Eventually.of_forall (fun t => f.norm_coe_le_norm _)
      _ = _ := by simp
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : ℝ => ‖f‖)
    (fun n => (hm n).integral_prod_right.aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall (fun x => tendsto_integral_affine_cauchy f x hγ))
  simpa only [integral_cauchyRegularization_eq μ f _ (hγne _)] using ht

end MeasureTheory

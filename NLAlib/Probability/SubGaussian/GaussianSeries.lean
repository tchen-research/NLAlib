import NLAlib.Probability.SubGaussian.GaussianConvex
import NLAlib.ForMathlib.MeasureTheory.AffineSeries

/-!
# Gaussian domination for finite independent subgaussian series

The actual exponential-square moment and centering assumptions imply a
dimension-free comparison in any real normed space. Finite-product coordinate
replacement uses the affine scalar comparison, preserving the factor `10K`.
Source: the scalar domination reroute for iterated matrix Khintchine.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Independent centered scalar product laws with exponential-square parameter
`K` are dominated by scaled Gaussian coordinates inside an affine series norm.
The laws may differ across coordinates. Source: the scalar domination reroute.
atlas: subgaussian-gaussian-series-comparison (partial) -/
theorem integral_norm_add_sum_smul_pi_le_gaussian_of_lintegral_exp_sq
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (K : ℝ) (hK : 0 < K)
    (hmean : ∀ i, ∫ x : ℝ, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (z : E) (a : ι → E) :
    (∫ x : ι → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi ν) ≤
      ∫ g : ι → ℝ, ‖z + (10 * K) • (∑ i, g i • a i)‖ ∂gaussianVector ι := by
  let c : ℝ := 10 * K
  let η : ι → Measure ℝ := fun _ => (gaussianReal 0 1).map (fun g : ℝ => c * g)
  have hp : ∀ i, IsProbabilityMeasure (η i) := fun _ =>
    (gaussianReal 0 1).isProbabilityMeasure_map (by fun_prop)
  have hg : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hν : ∀ i, Integrable (id : ℝ → ℝ) (ν i) := fun i =>
    (hasSubgaussianMGF_of_lintegral_exp_sq_le_two aemeasurable_id K hK (hmean i)
      (hpsi i)).memLp 1 |>.integrable le_rfl
  have hη : ∀ i, Integrable (id : ℝ → ℝ) (η i) := by
    intro i
    apply (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).mpr
    simpa only [Function.comp_def, id_eq] using hg.const_mul c
  have hstep : ∀ i (w : E), (∫ t : ℝ, ‖w + t • a i‖ ∂ν i) ≤
      ∫ t : ℝ, ‖w + t • a i‖ ∂η i := by
    intro i w
    change _ ≤ ∫ t : ℝ, ‖w + t • a i‖ ∂(gaussianReal 0 1).map (fun g : ℝ => c * g)
    rw [integral_map (by fun_prop) (by fun_prop)]
    exact integral_norm_add_smul_le_gaussian_of_lintegral_exp_sq K hK (hmean i)
      (hpsi i) w (a i)
  have hi := @MeasureTheory.integral_norm_add_sum_smul_pi_le E _ _ ι _ ν η inferInstance hp hν hη a hstep z
  have hm : MeasurePreserving (fun g : ι → ℝ => fun i => c * g i)
      (gaussianVector ι) (Measure.pi η) := by
    exact measurePreserving_pi (fun _ : ι => gaussianReal 0 1) η
      (fun _ => ⟨by fun_prop, rfl⟩)
  have he : (∫ x : ι → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi η) =
      ∫ g : ι → ℝ, ‖z + ∑ i, (c * g i) • a i‖ ∂gaussianVector ι := by
    have hc : Continuous (fun x : ι → ℝ => ‖z + ∑ i, x i • a i‖) := by fun_prop
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hc.measurable.aestronglyMeasurable]
  have hf (g : ι → ℝ) : (∑ i, (c * g i) • a i) = c • ∑ i, g i • a i := by
    simp only [mul_smul, Finset.smul_sum]
  simp only [hf] at he
  rw [he] at hi
  exact hi

/-- A finite independent centered subgaussian series has expected norm at most
`10K` times the Gaussian-series expectation, under actual exponential-square
moment bounds. Source: the scalar domination reroute; supports the matrix-chaos
Khintchine cards without a general subgaussian-process theorem.
atlas: subgaussian-gaussian-series-comparison (partial) -/
theorem integral_norm_sum_smul_pi_le_gaussian_of_lintegral_exp_sq
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (K : ℝ) (hK : 0 < K)
    (hmean : ∀ i, ∫ x : ℝ, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (a : ι → E) :
    (∫ x : ι → ℝ, ‖∑ i, x i • a i‖ ∂Measure.pi ν) ≤
      (10 * K) * ∫ g : ι → ℝ, ‖∑ i, g i • a i‖ ∂gaussianVector ι := by
  have h := integral_norm_add_sum_smul_pi_le_gaussian_of_lintegral_exp_sq ν K hK hmean hpsi (0 : E) a
  simpa only [zero_add, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 10 * K),
    integral_const_mul] using h

end NLAlib

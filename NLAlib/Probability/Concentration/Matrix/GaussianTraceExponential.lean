import NLAlib.Matrix.Functions.TraceExponentialTaylor
import NLAlib.Matrix.Functions.TraceExpBounds
import NLAlib.ForMathlib.Probability.GaussianExponentialMoments
import NLAlib.Probability.Concentration.Matrix.TraceExponentialCovariance

/-!
# Gaussian trace-exponential integrability and quadratic lower comparison

Gaussian norm exponential moments justify the expectations in BMV replacement.
For centered Gaussian Hermitian perturbations, symmetry removes all odd terms
before integration and gives the exact quadratic Taylor lower estimate.
Source: Tropp (2026), Section 4.6, reorganized through symmetric perturbations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian trace exponential with a deterministic Hermitian offset is
integrable under every Gaussian matrix law, including degenerate covariances.
The self-adjointness condition is only required almost everywhere. -/
theorem integrable_traceExp_add_gaussian
    (μ : Measure (Matrix n n ℂ)) [IsGaussian μ]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hH : ∀ᵐ H ∂μ, H.IsHermitian) :
    Integrable (fun H => traceExp (A + H)) μ := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    have hzero (B : Matrix n n ℂ) : traceExp B = 0 := by simp [traceExp, Matrix.trace]
    simpa only [hzero] using (integrable_const (0 : ℝ) : Integrable (fun _ => (0 : ℝ)) μ)
  | inr hn =>
    have := hn
    refine ((IsGaussian.integrable_exp_mul_norm μ 1).const_mul (traceExp A)).mono'
      (((contDiff_traceExp (k := 1)).continuous.comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)
      ?_
    filter_upwards [hH] with H hH
    rw [Real.norm_eq_abs, abs_of_nonneg (traceExp_nonneg_of_isHermitian _ (hA.add hH))]
    have hb := traceExp_le_exp_mul_traceExp_of_norm_sub_le (A + H) A (hA.add hH) hA
      (δ := ‖H‖) (by simp)
    simpa only [one_mul, mul_comm, mul_one] using hb

open scoped Matrix.Norms.L2Operator in
/-- Full real matrix coordinates of a Gaussian matrix have finite second
moments, as needed by the trace-exponential covariance contraction. -/
theorem memLp_two_matrixRealCoordinates_gaussian
    (μ : Measure (Matrix n n ℂ)) [IsGaussian μ] :
    MemLp (fun H : Matrix n n ℂ => matrixRealCoordinates H) 2 μ := by
  exact (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap
    |>.comp_memLp' (IsGaussian.memLp_two_id (μ := μ))

open scoped Matrix.Norms.L2Operator in
/-- Any centrally symmetric Hermitian matrix law dominates its quadratic
trace-exponential Taylor term when the observable and the quadratic term are
integrable. Gaussian integrability is discharged in the following corollary. -/
theorem traceExp_add_half_integral_iteratedDeriv_two_le_integral_of_map_neg_eq
    (μ : Measure (Matrix n n ℂ)) [IsProbabilityMeasure μ]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hH : ∀ᵐ H ∂μ, H.IsHermitian)
    (hneg : μ.map (fun H : Matrix n n ℂ => -H) = μ)
    (hplus : Integrable (fun H => traceExp (A + H)) μ)
    (hsecond : Integrable
      (fun H => iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • H)) 0) μ) :
    traceExp A + (1 / 2) *
      (∫ H, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • H)) 0 ∂μ) ≤
      ∫ H, traceExp (A + H) ∂μ := by
  have hmap : Integrable (fun H => traceExp (A + H))
      (μ.map (fun H : Matrix n n ℂ => -H)) := by
    rw [hneg]
    exact hplus
  have hminus : Integrable (fun H => traceExp (A - H)) μ := by
    simpa only [Function.comp_def, sub_eq_add_neg] using hmap.comp_measurable (by fun_prop)
  have hbound := integral_mono_ae
    ((integrable_const (2 * traceExp A)).add hsecond)
    (hplus.add hminus)
    (hH.mono fun H hherm => two_mul_traceExp_add_iteratedDeriv_two_le_add_traceExp A H hA hherm)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (integrable_const _) hsecond, integral_add hplus hminus,
    integral_const, probReal_univ, one_smul] at hbound
  have hsym : (∫ H, traceExp (A - H) ∂μ) = ∫ H, traceExp (A + H) ∂μ := by
    have hi := integral_map (by fun_prop : AEMeasurable (fun H : Matrix n n ℂ => -H) μ)
      hmap.aestronglyMeasurable
    simpa only [hneg, sub_eq_add_neg] using hi.symm
  rw [hsym] at hbound
  linarith

open scoped Matrix.Norms.L2Operator in
/-- Centered Gaussian Hermitian perturbations dominate the exact second-order
Taylor term in expectation. Integrability of both sides is proved from the
Gaussian law; no exponential-moment or derivative-integrability hypothesis
is imposed. Source: Tropp (2026), Section 4.6.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem traceExp_add_half_integral_iteratedDeriv_two_le_integral_gaussian
    (μ : Measure (Matrix n n ℂ)) [IsGaussian μ]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hH : ∀ᵐ H ∂μ, H.IsHermitian) (hmean : ∫ H, H ∂μ = 0) :
    traceExp A + (1 / 2) *
      (∫ H, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • H)) 0 ∂μ) ≤
      ∫ H, traceExp (A + H) ∂μ :=
  traceExp_add_half_integral_iteratedDeriv_two_le_integral_of_map_neg_eq μ A hA hH
    (IsGaussian.map_neg_eq_self_of_integral_eq_zero μ hmean)
    (integrable_traceExp_add_gaussian μ A hA hH)
    (integrable_iteratedDeriv_two_traceExp_add_smul A
      (memLp_two_matrixRealCoordinates_gaussian μ))

open scoped Matrix.Norms.L2Operator in
/-- The Gaussian quadratic lower comparison after an arbitrary real scalar
rescaling. The coefficient is exactly the squared scale divided by two,
including a zero scale and degenerate Gaussian laws.
Source: Tropp (2026), Section 4.6.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem traceExp_add_sq_div_two_mul_integral_iteratedDeriv_two_le_integral_gaussian
    (μ : Measure (Matrix n n ℂ)) [IsGaussian μ]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hH : ∀ᵐ H ∂μ, H.IsHermitian) (hmean : ∫ H, H ∂μ = 0) (c : ℝ) :
    traceExp A + (c ^ 2 / 2) *
      (∫ H, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • H)) 0 ∂μ) ≤
      ∫ H, traceExp (A + c • H) ∂μ := by
  let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := c • ContinuousLinearMap.id ℝ _
  have hL (H : Matrix n n ℂ) : L H = c • H := rfl
  have hherm : ∀ᵐ H ∂μ.map L, H.IsHermitian := by
    apply (ae_map_iff L.continuous.measurable.aemeasurable ?_).mpr
    · filter_upwards [hH] with H hH
      simpa only [hL] using hH.smul (IsSelfAdjoint.all c)
    · exact (isClosed_eq (by fun_prop : Continuous (fun H : Matrix n n ℂ => Hᴴ))
        continuous_id).measurableSet
  have hmeanL : (∫ H, H ∂μ.map L) = 0 := by
    change (∫ H, id H ∂μ.map L) = 0
    rw [integral_map L.continuous.measurable.aemeasurable aestronglyMeasurable_id]
    have hi := L.integral_comp_comm (IsGaussian.integrable_id (μ := μ))
    simpa only [id_eq, hmean, map_zero] using hi
  have h := traceExp_add_half_integral_iteratedDeriv_two_le_integral_gaussian
    (μ.map L) A hA hherm hmeanL
  have hplus := integrable_traceExp_add_gaussian (μ.map L) A hA hherm
  have hsecond := integrable_iteratedDeriv_two_traceExp_add_smul A
    (memLp_two_matrixRealCoordinates_gaussian (μ.map L))
  rw [integral_map L.continuous.measurable.aemeasurable hplus.aestronglyMeasurable,
    integral_map L.continuous.measurable.aemeasurable hsecond.aestronglyMeasurable] at h
  simp only [hL] at h
  simp_rw [iteratedDeriv_two_traceExp_add_smul_smul_zero] at h
  rw [integral_const_mul] at h
  convert! h using 1
  ring

open scoped Matrix.Norms.L2Operator in
/-- An arbitrary real multiple of a Hermitian Gaussian perturbation has an
integrable trace exponential at every deterministic Hermitian offset. -/
theorem integrable_traceExp_add_smul_gaussian
    (μ : Measure (Matrix n n ℂ)) [IsGaussian μ]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hH : ∀ᵐ H ∂μ, H.IsHermitian) (c : ℝ) :
    Integrable (fun H => traceExp (A + c • H)) μ := by
  let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := c • ContinuousLinearMap.id ℝ _
  have hherm : ∀ᵐ H ∂μ.map L, H.IsHermitian := by
    apply (ae_map_iff L.continuous.measurable.aemeasurable ?_).mpr
    · filter_upwards [hH] with H hH
      exact hH.smul (IsSelfAdjoint.all c)
    · exact (isClosed_eq (by fun_prop : Continuous (fun H : Matrix n n ℂ => Hᴴ))
        continuous_id).measurableSet
  have hi := integrable_traceExp_add_gaussian (μ.map L) A hA hherm
  exact hi.comp_measurable L.continuous.measurable

end NLAlib

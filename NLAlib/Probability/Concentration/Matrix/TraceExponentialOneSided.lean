import NLAlib.Probability.Concentration.Matrix.TraceExponentialCovariance
import NLAlib.Matrix.Functions.TraceExponentialTaylor
import NLAlib.Matrix.Functions.TraceExpBounds

/-!
# Centered one-sided trace-exponential Taylor comparison

Actual centered square-integrable matrix laws satisfy the BMV Taylor upper
estimate under only a one-sided Loewner bound. The linear term vanishes through
the actual continuous real derivative and the mean, rather than an assumed
cancellation. This is the non-Gaussian half of Tropp (2026), Section 4.6.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- An almost surely upper-bounded Hermitian perturbation has an integrable
trace exponential at every deterministic Hermitian offset. No norm moments,
lower bound, or nonempty matrix dimension is needed. -/
theorem integrable_traceExp_add_of_ae_upper_bound
    (A : M) (hA : A.IsHermitian) {X : Ω → M}
    (hXmeas : AEStronglyMeasurable X μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {R : ℝ} (hbound : ∀ᵐ ω ∂μ, X ω ≤ R • (1 : M)) :
    Integrable (fun ω => traceExp (A + X ω)) μ := by
  have hR : (R • (1 : M)).IsHermitian := Matrix.isHermitian_one.smul (IsSelfAdjoint.all R)
  refine Integrable.of_bound
    (continuous_traceExp.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.add hXmeas))
    (traceExp (A + R • (1 : M))) ?_
  filter_upwards [hHerm, hbound] with ω hω hωb
  rw [Real.norm_eq_abs, abs_of_nonneg (traceExp_nonneg_of_isHermitian _ (hA.add hω))]
  exact traceExp_le_traceExp _ _ (hA.add hω) (hA.add hR) (add_le_add le_rfl hωb)

open scoped Matrix.Norms.L2Operator in
omit [IsProbabilityMeasure μ] in
/-- Finite first entry moments ensure integrability of the actual first
directional trace derivative at any deterministic offset. -/
theorem integrable_deriv_traceExp_add_smul_zero
    (A : M) {X : Ω → M}
    (hX : Integrable (fun ω => matrixRealCoordinates (X ω)) μ) :
    Integrable (fun ω => deriv (fun t : ℝ => traceExp (A + t • X ω)) 0) μ := by
  let C := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm.toContinuousLinearMap
  let L := (fderiv ℝ traceExp A).comp C
  have h := L.integrable_comp hX
  simpa only [L, C, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    matrixRealCoordinatesContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.symm_apply_apply, deriv_traceExp_add_smul_zero_eq_fderiv] using h

open scoped Matrix.Norms.L2Operator in
omit [IsProbabilityMeasure μ] in
/-- Centered full entry coordinates cancel the actual first directional
trace derivative in expectation. -/
theorem integral_deriv_traceExp_add_smul_zero_eq_zero
    (A : M) {X : Ω → M}
    (hX : Integrable (fun ω => matrixRealCoordinates (X ω)) μ)
    (hmean : (∫ ω, matrixRealCoordinates (X ω) ∂μ) = 0) :
    (∫ ω, deriv (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) = 0 := by
  let C := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm.toContinuousLinearMap
  let L := (fderiv ℝ traceExp A).comp C
  have h := L.integral_comp_comm hX
  rw [hmean, map_zero] at h
  simpa only [L, C, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    matrixRealCoordinatesContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.symm_apply_apply, deriv_traceExp_add_smul_zero_eq_fderiv] using h

open scoped Matrix.Norms.L2Operator in
/-- A centered, square-integrable Hermitian perturbation has the BMV Taylor
upper expectation estimate from its original one-sided upper Loewner bound.
No lower bound or negative exponential moment of the perturbation is required.
Source: Tropp (2026), Section 4.6.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_traceExp_add_le_traceExp_add_integral_iteratedDeriv_two_mul_coefficient
    (A : M) (hA : A.IsHermitian) {X : Ω → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hmean : (∫ ω, matrixRealCoordinates (X ω) ∂μ) = 0)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {R : ℝ} (hbound : ∀ᵐ ω ∂μ, X ω ≤ R • (1 : M)) :
    (∫ ω, traceExp (A + X ω) ∂μ) ≤ traceExp A +
      (∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) *
        expSecondRemainderCoefficient R := by
  classical
  have hXi := hX.integrable one_le_two
  have hfirst := integrable_deriv_traceExp_add_smul_zero A hXi
  have hsecond := integrable_iteratedDeriv_two_traceExp_add_smul A hX
  have hupper : Integrable (fun ω => traceExp A +
      deriv (fun t : ℝ => traceExp (A + t • X ω)) 0 +
      iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 *
        expSecondRemainderCoefficient R) μ :=
    ((integrable_const (traceExp A)).add hfirst).add (hsecond.mul_const (expSecondRemainderCoefficient R))
  have hXmeas : AEStronglyMeasurable X μ := by
    let C := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm
    have hh := C.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable
    simpa only [C, matrixRealCoordinatesContinuousLinearEquiv,
      LinearEquiv.coe_toContinuousLinearEquiv_symm', LinearEquiv.symm_apply_apply] using hh
  have hi : Integrable (fun ω => traceExp (A + X ω)) μ := by
    refine hupper.mono' (continuous_traceExp.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.add hXmeas)) ?_
    filter_upwards [hHerm, hbound] with ω hω hωb
    rw [Real.norm_eq_abs, abs_of_nonneg (traceExp_nonneg_of_isHermitian _ (hA.add hω))]
    exact traceExp_add_le_add_deriv_add_iteratedDeriv_two_mul_coefficient_of_le A (X ω) hA hω hωb
  have hle := integral_mono_ae hi hupper (by
    filter_upwards [hHerm, hbound] with ω hω hωb
    exact traceExp_add_le_add_deriv_add_iteratedDeriv_two_mul_coefficient_of_le A (X ω) hA hω hωb)
  have hs := integral_add ((integrable_const (traceExp A)).add hfirst)
    (hsecond.mul_const (expSecondRemainderCoefficient R))
  have hsfirst := integral_add (integrable_const (traceExp A)) hfirst
  simp only [Pi.add_apply] at hs hsfirst
  rw [hs, hsfirst, integral_const,
    probReal_univ, one_smul, integral_deriv_traceExp_add_smul_zero_eq_zero A hXi hmean,
    integral_mul_const, add_zero] at hle
  exact hle

end NLAlib

import NLAlib.Matrix.Functions.TraceExponentialDerivatives
import NLAlib.Matrix.Basic.RealCoordinates
import NLAlib.ForMathlib.Probability.QuadraticCovariance

/-!
# Trace-exponential Hessians and full entry covariance

The second directional derivative of the trace exponential has an expectation
which is determined by every real and imaginary entry covariance and mean.
This is the exact quadratic identity needed by the BMV Gaussian comparison;
matching only the expected matrix square is not used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {n Ω Ω' : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
omit [IsProbabilityMeasure μ] in
/-- Second moments of the full real matrix coordinates ensure integrability
of the actual second directional trace-exponential derivative. -/
theorem integrable_iteratedDeriv_two_traceExp_add_smul
    (A : M) {X : Ω → M} (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ) :
    Integrable (fun ω => iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0) μ := by
  let C := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm.toContinuousLinearMap
  let B := (traceExpHessian A).bilinearComp C C
  have h := integrable_bilin_quadratic_of_memLp_two B hX
  simpa only [B, ContinuousLinearMap.bilinearComp_apply, C,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    matrixRealCoordinatesContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv_symm',
    iteratedDeriv_two_traceExp_add_smul_zero_eq_hessian] using h

open scoped Matrix.Norms.L2Operator in
omit [IsProbabilityMeasure μ] in
/-- The expected second directional trace derivative is the exact contraction
with all products of real and imaginary matrix-entry coordinates. -/
theorem integral_iteratedDeriv_two_traceExp_add_smul_eq_sum_second_moments
    (A : M) {X : Ω → M} (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ) :
    (∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) =
      ∑ i : J, ∑ j : J,
        (∫ ω, matrixRealCoordinates (X ω) i * matrixRealCoordinates (X ω) j ∂μ) *
        traceExpHessian A (matrixRealCoordinates.symm (Pi.single i 1))
          (matrixRealCoordinates.symm (Pi.single j 1)) := by
  let C := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm.toContinuousLinearMap
  let B := (traceExpHessian A).bilinearComp C C
  have h := integral_bilin_quadratic_eq_sum_second_moments B hX
  simpa only [B, ContinuousLinearMap.bilinearComp_apply, C,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    matrixRealCoordinatesContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv_symm',
    iteratedDeriv_two_traceExp_add_smul_zero_eq_hessian] using h

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Matching all actual coordinate second moments identifies the expected
second trace derivative at every deterministic offset. -/
theorem integral_iteratedDeriv_two_traceExp_add_smul_eq_of_second_moments_eq
    (A : M) {X : Ω → M} {Z : Ω' → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hZ : MemLp (fun ω => matrixRealCoordinates (Z ω)) 2 ν)
    (hmatch : ∀ i j : J,
      (∫ ω, matrixRealCoordinates (X ω) i * matrixRealCoordinates (X ω) j ∂μ) =
        ∫ ω, matrixRealCoordinates (Z ω) i * matrixRealCoordinates (Z ω) j ∂ν) :
    (∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) =
      ∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • Z ω)) 0 ∂ν := by
  simp_rw [integral_iteratedDeriv_two_traceExp_add_smul_eq_sum_second_moments A hX,
    integral_iteratedDeriv_two_traceExp_add_smul_eq_sum_second_moments A hZ, hmatch]

/-- Full real-entry covariance and mean matching, including every mixed
real/imaginary pair, preserve the expected second directional trace derivative.
No Gaussianity or self-adjointness hypothesis is needed for this identity.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_iteratedDeriv_two_traceExp_add_smul_eq_of_mean_covariance_eq
    (A : M) {X : Ω → M} {Z : Ω' → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hZ : MemLp (fun ω => matrixRealCoordinates (Z ω)) 2 ν)
    (hmean : ∀ i : J,
      (∫ ω, matrixRealCoordinates (X ω) i ∂μ) = ∫ ω, matrixRealCoordinates (Z ω) i ∂ν)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates (X ω) i, fun ω => matrixRealCoordinates (X ω) j; μ] =
      cov[fun ω => matrixRealCoordinates (Z ω) i, fun ω => matrixRealCoordinates (Z ω) j; ν]) :
    (∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) =
      ∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • Z ω)) 0 ∂ν := by
  exact integral_iteratedDeriv_two_traceExp_add_smul_eq_of_second_moments_eq A hX hZ
    (integral_mul_coordinates_eq_of_mean_covariance_eq hX hZ hmean hcov)

/-- Centered matrix laws with matching full real-entry covariances have the
same expected second trace derivative at every deterministic offset.
Source: Tropp (2026), full covariance contraction in Gaussian replacement.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_iteratedDeriv_two_traceExp_add_smul_eq_of_centered_covariance_eq
    (A : M) {X : Ω → M} {Z : Ω' → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hZ : MemLp (fun ω => matrixRealCoordinates (Z ω)) 2 ν)
    (hXmean : (∫ ω, matrixRealCoordinates (X ω) ∂μ) = 0)
    (hZmean : (∫ ω, matrixRealCoordinates (Z ω) ∂ν) = 0)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates (X ω) i, fun ω => matrixRealCoordinates (X ω) j; μ] =
      cov[fun ω => matrixRealCoordinates (Z ω) i, fun ω => matrixRealCoordinates (Z ω) j; ν]) :
    (∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) =
      ∫ ω, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • Z ω)) 0 ∂ν := by
  apply integral_iteratedDeriv_two_traceExp_add_smul_eq_of_mean_covariance_eq A hX hZ _ hcov
  intro i
  have hx := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i).integral_comp_comm
    (hX.integrable one_le_two)
  have hz := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i).integral_comp_comm
    (hZ.integrable one_le_two)
  simp only [ContinuousLinearMap.proj_apply, hXmean, hZmean, Pi.zero_apply] at hx hz
  exact hx.trans hz.symm

end NLAlib

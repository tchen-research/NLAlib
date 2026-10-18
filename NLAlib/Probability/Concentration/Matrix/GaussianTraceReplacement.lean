import NLAlib.Probability.Concentration.Matrix.TraceExponentialOneSided
import NLAlib.Probability.Concentration.Matrix.GaussianTraceExponential
import NLAlib.Probability.Concentration.Matrix.GaussianTraceInflation

/-!
# One-sided covariance-matched Gaussian trace replacement

A centered Hermitian perturbation with only an upper Loewner bound is compared
against its actual centered Gaussian law with the same full real-entry
covariance. BMV supplies the exact continuous inflation coefficient. Finite
second moments suffice for the original perturbation, which may be unbounded
below. Source: Tropp (2026), Section 4.6.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- One-sided Gaussian replacement for one actual centered square-integrable
Hermitian perturbation, under matching all real and imaginary entry covariances.
The exact integral inflation includes zero upper bound and singular covariance.
Source: Tropp (2026), Section 4.6.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_traceExp_add_le_integral_traceExp_add_smul_gaussian
    (A : M) (hA : A.IsHermitian) {X : Ω → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hXmean : (∫ ω, matrixRealCoordinates (X ω) ∂μ) = 0)
    (hXHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {R : ℝ} (hbound : ∀ᵐ ω ∂μ, X ω ≤ R • (1 : M))
    (γ : Measure M) [IsGaussian γ]
    (hZHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hZmean : ∫ Z, Z ∂γ = 0)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates (X ω) i, fun ω => matrixRealCoordinates (X ω) j; μ] =
        cov[fun Z => matrixRealCoordinates Z i, fun Z => matrixRealCoordinates Z j; γ]) :
    (∫ ω, traceExp (A + X ω) ∂μ) ≤
      ∫ Z, traceExp (A + Real.sqrt (2 * expSecondRemainderCoefficient R) • Z) ∂γ := by
  have hZ := memLp_two_matrixRealCoordinates_gaussian γ
  have hZcoordinates : (∫ Z, matrixRealCoordinates Z ∂γ) = 0 := by
    have h := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).integral_comp_comm
      (fun Z : M => Z) (μ := γ)
    simpa only [matrixRealCoordinatesContinuousLinearEquiv,
      LinearEquiv.coe_toContinuousLinearEquiv', hZmean, map_zero] using h
  have hmeans (i : J) : (∫ ω, matrixRealCoordinates (X ω) i ∂μ) =
      ∫ Z, matrixRealCoordinates Z i ∂γ := by
    have hx := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i).integral_comp_comm
      (hX.integrable one_le_two)
    have hz := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i).integral_comp_comm
      (hZ.integrable one_le_two)
    simp only [ContinuousLinearMap.proj_apply, hXmean, hZcoordinates, Pi.zero_apply] at hx hz
    exact hx.trans hz.symm
  have heq := integral_iteratedDeriv_two_traceExp_add_smul_eq_of_mean_covariance_eq
    A hX hZ hmeans hcov
  have hu := integral_traceExp_add_le_traceExp_add_integral_iteratedDeriv_two_mul_coefficient
    A hA hX hXmean hXHerm hbound
  have hl := traceExp_add_sq_div_two_mul_integral_iteratedDeriv_two_le_integral_gaussian
    γ A hA hZHerm hZmean (Real.sqrt (2 * expSecondRemainderCoefficient R))
  have hs : Real.sqrt (2 * expSecondRemainderCoefficient R) ^ 2 / 2 =
      expSecondRemainderCoefficient R := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (expSecondRemainderCoefficient_nonneg R))]
    ring
  rw [hs] at hl
  calc
    _ ≤ traceExp A + (∫ ω, iteratedDeriv 2
          (fun t : ℝ => traceExp (A + t • X ω)) 0 ∂μ) *
          expSecondRemainderCoefficient R := hu
    _ = traceExp A + expSecondRemainderCoefficient R *
          (∫ Z, iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • Z)) 0 ∂γ) := by
      rw [heq]
      ring
    _ ≤ _ := hl

open scoped Matrix.Norms.L2Operator in
/-- One-summand Gaussian trace-MGF replacement at every nonnegative time,
using the exact continuous inflation `gaussianTraceInflation`. Only the
original upper Loewner bound and finite second moments are imposed on `X`.
Source: Tropp (2026), Propositions 4.5--4.6.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_traceExp_add_smul_le_integral_traceExp_add_gaussianTraceInflation
    (A : M) (hA : A.IsHermitian) {X : Ω → M}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hXmean : (∫ ω, matrixRealCoordinates (X ω) ∂μ) = 0)
    (hXHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {R : ℝ} (hbound : ∀ᵐ ω ∂μ, X ω ≤ R • (1 : M))
    (γ : Measure M) [IsGaussian γ]
    (hZHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hZmean : ∫ Z, Z ∂γ = 0)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates (X ω) i, fun ω => matrixRealCoordinates (X ω) j; μ] =
        cov[fun Z => matrixRealCoordinates Z i, fun Z => matrixRealCoordinates Z j; γ])
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ ω, traceExp (A + θ • X ω) ∂μ) ≤
      ∫ Z, traceExp (A + gaussianTraceInflation R θ • Z) ∂γ := by
  have hZ := memLp_two_matrixRealCoordinates_gaussian γ
  have hZcoordinates : (∫ Z, matrixRealCoordinates Z ∂γ) = 0 := by
    have h := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).integral_comp_comm
      (fun Z : M => Z) (μ := γ)
    simpa only [matrixRealCoordinatesContinuousLinearEquiv,
      LinearEquiv.coe_toContinuousLinearEquiv', hZmean, map_zero] using h
  have heq := integral_iteratedDeriv_two_traceExp_add_smul_eq_of_centered_covariance_eq
    A hX hZ hXmean hZcoordinates hcov
  have hθX : MemLp (fun ω => matrixRealCoordinates (θ • X ω)) 2 μ := by
    convert! hX.const_smul θ using 1
    ext ω
    simp only [map_smul, Pi.smul_apply]
  have hθmean : (∫ ω, matrixRealCoordinates (θ • X ω) ∂μ) = 0 := by
    simp_rw [map_smul]
    rw [integral_smul, hXmean, smul_zero]
  have hθHerm : ∀ᵐ ω ∂μ, (θ • X ω).IsHermitian :=
    hXHerm.mono fun _ hH => hH.smul (IsSelfAdjoint.all θ)
  have hθbound : ∀ᵐ ω ∂μ, θ • X ω ≤ (θ * R) • (1 : M) := by
    filter_upwards [hbound] with ω hω
    simpa only [smul_smul] using Matrix.matrix_smul_le_smul_of_nonneg hω hθ
  have hu := integral_traceExp_add_le_traceExp_add_integral_iteratedDeriv_two_mul_coefficient
    A hA hθX hθmean hθHerm hθbound
  have hl := traceExp_add_sq_div_two_mul_integral_iteratedDeriv_two_le_integral_gaussian
    γ A hA hZHerm hZmean (gaussianTraceInflation R θ)
  rw [gaussianTraceInflation_sq_div_two] at hl
  simp_rw [iteratedDeriv_two_traceExp_add_smul_smul_zero] at hu
  rw [integral_const_mul, heq] at hu
  nlinarith [hu, hl]

end NLAlib

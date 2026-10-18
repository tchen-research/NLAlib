import NLAlib.Probability.Concentration.Matrix.GaussianTraceReplacement
import NLAlib.ForMathlib.MeasureTheory.IndependentReplacement
import NLAlib.Probability.Gaussian.Basic.CovarianceProxy
import NLAlib.Probability.Gaussian.Basic.MatrixSumCovariance

/-!
# Gaussian trace replacement for finite independent product laws

The genuine one-summand BMV comparison is applied at random offsets using
Tonelli's theorem. Only positive trace exponentials are integrated during the
replacement, so negative exponential moments of the original summands are
not introduced.
Source: Tropp (2026), Proposition 4.8.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Finite independent one-sided summands can all be replaced by their actual
centered Gaussian covariance proxies. The conclusion first uses nonnegative
integrals, avoiding any integrability assumption on intermediate hybrids.
Every mixed real/imaginary entry covariance is matched for each summand.
Source: Tropp (2026), Proposition 4.8.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem lintegral_traceExp_add_smul_sum_le_gaussianTraceInflation_sum
    {N : ℕ} (ν γ : Fin N → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsGaussian (γ i)]
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ W, matrixRealCoordinates W ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ W ∂ν i, W.IsHermitian)
    {R : ℝ} (hbound : ∀ i, ∀ᵐ W ∂ν i, W ≤ R • (1 : M))
    (hγHerm : ∀ i, ∀ᵐ Z ∂γ i, Z.IsHermitian)
    (hγmean : ∀ i, (∫ Z, Z ∂γ i) = 0)
    (hcov : ∀ i a b,
      cov[fun W => matrixRealCoordinates W a, fun W => matrixRealCoordinates W b; ν i] =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ i])
    (A : M) (hA : A.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫⁻ W, ENNReal.ofReal (traceExp (A + θ • ∑ i, W i)) ∂Measure.pi ν) ≤
      ∫⁻ Z, ENNReal.ofReal (traceExp (A + gaussianTraceInflation R θ • ∑ i, Z i))
        ∂Measure.pi γ := by
  let g := gaussianTraceInflation R θ
  have hstep (i : Fin N) (B : M) (hB : B ∈ selfAdjoint M) :
      (∫⁻ W, ENNReal.ofReal (traceExp (B + θ • W)) ∂ν i) ≤
        ∫⁻ Z, ENNReal.ofReal (traceExp (B + g • Z)) ∂γ i := by
    change B.IsHermitian at hB
    have hθHerm : ∀ᵐ W ∂ν i, (θ • W).IsHermitian :=
      (hνHerm i).mono fun W hW => hW.smul (IsSelfAdjoint.all θ)
    have hθbound : ∀ᵐ W ∂ν i, θ • W ≤ (θ * R) • (1 : M) := by
      filter_upwards [hbound i] with W hW
      simpa only [smul_smul] using Matrix.matrix_smul_le_smul_of_nonneg hW hθ
    have hiW : Integrable (fun W : M => traceExp (B + θ • W)) (ν i) :=
      integrable_traceExp_add_of_ae_upper_bound B hB
        (show Continuous (fun W : M => θ • W) from by fun_prop).aestronglyMeasurable
        hθHerm hθbound
    have hiZ := integrable_traceExp_add_smul_gaussian (γ i) B hB (hγHerm i) g
    have hnW : 0 ≤ᵐ[ν i] (fun W => traceExp (B + θ • W)) :=
      hθHerm.mono fun W hW => traceExp_nonneg_of_isHermitian _ (hB.add hW)
    have hnZ : 0 ≤ᵐ[γ i] (fun Z => traceExp (B + g • Z)) :=
      (hγHerm i).mono fun Z hZ =>
        traceExp_nonneg_of_isHermitian _ (hB.add (hZ.smul (IsSelfAdjoint.all g)))
    rw [← ofReal_integral_eq_lintegral_ofReal hiW hnW,
      ← ofReal_integral_eq_lintegral_ofReal hiZ hnZ]
    exact ENNReal.ofReal_le_ofReal
      (integral_traceExp_add_smul_le_integral_traceExp_add_gaussianTraceInflation
        B hB (hν2 i) (hνmean i) (hνHerm i) (hbound i) (γ i) (hγHerm i) (hγmean i)
        (hcov i) hθ)
  have h := lintegral_add_sum_apply_pi_le_of_lintegral_add_apply_le ν γ
    (selfAdjoint M) (fun _ W => θ • W) (fun _ Z => g • Z)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun i => (hνHerm i).mono fun W hW => hW.smul (IsSelfAdjoint.all θ))
    (fun i => (hγHerm i).mono fun Z hZ => hZ.smul (IsSelfAdjoint.all g))
    (fun B => ENNReal.ofReal (traceExp B))
    (by exact ENNReal.measurable_ofReal.comp continuous_traceExp.measurable)
    hstep A hA
  simpa only [← Finset.smul_sum] using h

open scoped Matrix.Norms.L2Operator in
/-- Independent centered one-sided summands obey Gaussian trace-MGF comparison
against any centered Gaussian matrix law with their total full entry covariance.
Individual Gaussian proxies are constructed and their independent sum is
identified with the supplied law; proxy existence is not an assumption.
The product-law interface includes empty families and singular covariance.
Source: Tropp (2026), Proposition 4.8.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem integral_traceExp_add_smul_sum_pi_le_gaussianTraceInflation
    {N : ℕ} (ν : Fin N → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ W, W ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ W ∂ν i, W.IsHermitian)
    {R : ℝ} (hbound : ∀ i, ∀ᵐ W ∂ν i, W ≤ R • (1 : M))
    (ρ : Measure M) [IsGaussian ρ]
    (hρHerm : ∀ᵐ Z ∂ρ, Z.IsHermitian) (hρmean : (∫ Z, Z ∂ρ) = 0)
    (hρcov : ∀ a b,
      (∑ i, cov[fun W => matrixRealCoordinates W a, fun W => matrixRealCoordinates W b; ν i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; ρ])
    (A : M) (hA : A.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ W, traceExp (A + θ • ∑ i, W i) ∂Measure.pi ν) ≤
      ∫ Z, traceExp (A + gaussianTraceInflation R θ • Z) ∂ρ := by
  classical
  choose γ hγ hγmean hγHerm hγcov using fun i =>
    exists_isGaussian_hermitian_integral_eq_zero_covariance_eq
      (ν i) (hν2 i) (hνmean i) (hνHerm i)
  let (i : Fin N) : IsGaussian (γ i) := hγ i
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  have hνint (i : Fin N) : Integrable (fun W : M => W) (ν i) := by
    have hi := C.symm.toContinuousLinearMap.comp_memLp' (hν2 i)
    have he (W : M) : C.symm (matrixRealCoordinates W) = W :=
      matrixRealCoordinates.symm_apply_apply W
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, he] using
      hi.integrable one_le_two
  have hνcoordsmean (i : Fin N) : (∫ W, matrixRealCoordinates W ∂ν i) = 0 := by
    change (∫ W, C W ∂ν i) = 0
    have hc := C.toContinuousLinearMap.integral_comp_comm (hνint i)
    change (∫ W, C W ∂ν i) = C (∫ W, W ∂ν i) at hc
    rw [hc, hνmean i, map_zero]
  have hmap : (Measure.pi γ).map (fun Z : Fin N → M => ∑ i, Z i) = ρ := by
    apply map_sum_pi_gaussian_eq_of_covariance_eq γ ρ hγmean hρmean
    intro a b
    simpa only [hγcov] using hρcov a b
  have hlin := lintegral_traceExp_add_smul_sum_le_gaussianTraceInflation_sum
    ν γ hν2 hνcoordsmean hνHerm hbound hγHerm hγmean
    (fun i a b => (hγcov i a b).symm) A hA hθ
  have hright : (∫⁻ Z, ENNReal.ofReal
      (traceExp (A + gaussianTraceInflation R θ • ∑ i, Z i)) ∂Measure.pi γ) =
      ∫⁻ Z, ENNReal.ofReal (traceExp (A + gaussianTraceInflation R θ • Z)) ∂ρ := by
    rw [← hmap]
    symm
    exact lintegral_map
      (f := fun Z : M => ENNReal.ofReal (traceExp (A + gaussianTraceInflation R θ • Z)))
      (g := fun Z : Fin N → M => ∑ i, Z i)
      (ENNReal.measurable_ofReal.comp
        (continuous_traceExp.comp (by fun_prop)).measurable) (by fun_prop)
  rw [hright] at hlin
  have hnleft : 0 ≤ᵐ[Measure.pi ν] (fun W : Fin N → M => traceExp (A + θ • ∑ i, W i)) := by
    have hs : ∀ᵐ W ∂Measure.pi ν, ∀ i, (W i).IsHermitian :=
      ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hνHerm i))
    filter_upwards [hs] with W hW
    have hsum : (∑ i, W i).IsHermitian := by
      change (∑ i, W i)ᴴ = ∑ i, W i
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl (fun i _ => hW i)
    exact traceExp_nonneg_of_isHermitian _ (hA.add (hsum.smul (IsSelfAdjoint.all θ)))
  have hnright : 0 ≤ᵐ[ρ] (fun Z => traceExp (A + gaussianTraceInflation R θ • Z)) :=
    hρHerm.mono fun Z hZ => traceExp_nonneg_of_isHermitian _
      (hA.add (hZ.smul (IsSelfAdjoint.all _)))
  have hiright := integrable_traceExp_add_smul_gaussian ρ A hA hρHerm
    (gaussianTraceInflation R θ)
  have hfinite : (∫⁻ Z, ENNReal.ofReal (traceExp (A + gaussianTraceInflation R θ • Z)) ∂ρ) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hiright hnright]
    exact ENNReal.ofReal_ne_top
  rw [integral_eq_lintegral_of_nonneg_ae hnleft
      (continuous_traceExp.comp (by fun_prop)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnright hiright.aestronglyMeasurable]
  exact ENNReal.toReal_mono hfinite hlin

open scoped Matrix.Norms.L2Operator in
/-- Gaussian trace-MGF comparison for actual independent random matrices with
specified marginal laws and an actual Gaussian proxy on any probability space.
The covariance hypothesis is written as the sum of all marginal real-entry
covariances, exactly the full covariance of the independent sum.
Source: Tropp (2026), Proposition 4.8.
atlas: gaussian-trace-mgf-comparison -/
theorem integral_traceExp_smul_sum_add_le_gaussianTraceInflation_of_hasLaw
    {N : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    (W : Fin N → Ω → M) (ν : Fin N → Measure M)
    (hW : ∀ i, HasLaw (W i) (ν i) P) (hind : iIndepFun W P)
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ H, H ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ H ∂ν i, H.IsHermitian)
    {R : ℝ} (hbound : ∀ i, ∀ᵐ H ∂ν i, H ≤ R • (1 : M))
    (Z : Ω' → M) (ρ : Measure M) [IsGaussian ρ] (hZ : HasLaw Z ρ Q)
    (hρHerm : ∀ᵐ H ∂ρ, H.IsHermitian) (hρmean : (∫ H, H ∂ρ) = 0)
    (hρcov : ∀ a b,
      (∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i]) =
        cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ρ])
    (Δ : M) (hΔ : Δ.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ ω, traceExp (θ • ((∑ i, W i ω) + Δ)) ∂P) ≤
      ∫ ω, traceExp (gaussianTraceInflation R θ • Z ω + θ • Δ) ∂Q := by
  let (i : Fin N) : IsProbabilityMeasure (ν i) :=
    (hW i).isProbabilityMeasure_iff.mp inferInstance
  have hleft := (hind.hasLaw_pi hW).integral_comp
    (f := fun x : Fin N → M => traceExp (θ • Δ + θ • ∑ i, x i))
      (continuous_traceExp.comp (by fun_prop)).aestronglyMeasurable
  have hright := hZ.integral_comp
    (f := fun H : M => traceExp (θ • Δ + gaussianTraceInflation R θ • H))
      (continuous_traceExp.comp (by fun_prop)).aestronglyMeasurable
  have h := integral_traceExp_add_smul_sum_pi_le_gaussianTraceInflation
    ν hν2 hνmean hνHerm hbound ρ hρHerm hρmean hρcov
    (θ • Δ) (hΔ.smul (IsSelfAdjoint.all θ)) hθ
  rw [← hleft, ← hright] at h
  simpa only [Function.comp_def, smul_add, add_comm] using h

end NLAlib

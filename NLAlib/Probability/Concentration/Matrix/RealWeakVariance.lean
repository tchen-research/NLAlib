import NLAlib.Probability.Concentration.Matrix.WeakVariance
import NLAlib.Probability.Concentration.Matrix.QuadraticNet
import NLAlib.Probability.Concentration.Matrix.GaussianMaximumLaw
import NLAlib.Probability.Gaussian.Basic.RealMatrixSupport
import NLAlib.Matrix.Basic.RealQuadraticForm
import NLAlib.Matrix.Spectral.Complexification
import NLAlib.ForMathlib.Probability.VarianceBounds
import NLAlib.ForMathlib.Probability.QuadraticCovariance

/-!
# Real covariance proxies retain their quadratic variance and dimension

Full covariance matching with a real centered matrix law forces the complex
Gaussian proxy to be real almost surely. Real quadratic variance estimates
then control the native complex-unit-vector weak variance, without losing a
factor of two. The real sphere-net estimate controls its expected largest
eigenvalue. Source: Tropp (2026), Section 3.3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- A real Gaussian matrix law has the same quadratic variance budget for
complex unit test vectors as for real test vectors. Zero variance is included. -/
theorem quadraticWeakVariance_le_of_real_quadratic_variance
    (γ : Measure M) [IsGaussian γ]
    (hreal : ∀ᵐ A ∂γ, (Matrix.reCLM A).map Complex.ofReal = A)
    {c : ℝ} (hc : 0 ≤ c)
    (hvariance : ∀ u : n → ℝ,
      Var[fun A => quadForm (Matrix.reCLM A) u; γ] ≤ c * ‖WithLp.toLp 2 u‖ ^ 4) :
    quadraticWeakVariance γ ≤ c := by
  apply Real.sSup_le _ hc
  rintro _ ⟨u, hu, rfl⟩
  change Var[fun A => (quadForm A u).re; γ] ≤ c
  change ‖WithLp.toLp 2 u‖ = 1 at hu
  let a : n → ℝ := fun i => (u i).re
  let b : n → ℝ := fun i => (u i).im
  let X : M → ℝ := fun A => quadForm (Matrix.reCLM A) a
  let Y : M → ℝ := fun A => quadForm (Matrix.reCLM A) b
  have hX : MemLp X 2 γ :=
    ((quadFormContinuousLinearMap a).comp Matrix.reCLM).comp_memLp' IsGaussian.memLp_two_id
  have hY : MemLp Y 2 γ :=
    ((quadFormContinuousLinearMap b).comp Matrix.reCLM).comp_memLp' IsGaussian.memLp_two_id
  have he : (fun A => (quadForm A u).re) =ᵐ[γ] fun A => X A + Y A := by
    filter_upwards [hreal] with A hA
    simpa only [hA] using re_quadForm_map_ofReal (Matrix.reCLM A) u
  rw [variance_congr he]
  have hsum := variance_add_le_mul_sq_add_of_le_mul_sq hX hY hc
    (sq_nonneg ‖WithLp.toLp 2 a‖) (sq_nonneg ‖WithLp.toLp 2 b‖)
    (by simpa only [← pow_mul] using hvariance a)
    (by simpa only [← pow_mul] using hvariance b)
  have hn : ‖WithLp.toLp 2 a‖ ^ 2 + ‖WithLp.toLp 2 b‖ ^ 2 = 1 := by
    simpa only [a, b, hu, one_pow] using norm_toLp_re_sq_add_norm_toLp_im_sq u
  simpa only [hn, one_pow, mul_one] using hsum

open scoped Matrix.Norms.L2Operator in
/-- Full covariance matching transports the variance of each real quadratic
probe to the actual Gaussian proxy. Both laws have their genuine mean zero. -/
theorem variance_quadForm_reCLM_gaussian_eq_of_covariance_eq_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℝ) (hX : MemLp X 2 μ) (hmean : (∫ ω, X ω ∂μ) = 0)
    (γ : Measure M) [IsGaussian γ] (hγmean : (∫ A, A ∂γ) = 0)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) i,
        fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) j; μ] =
      cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; γ])
    (u : n → ℝ) :
    Var[fun A => quadForm (Matrix.reCLM A) u; γ] = Var[fun ω => quadForm (X ω) u; μ] := by
  let C : Matrix n n ℝ →L[ℝ] M :=
    (realMatrixComplexification (n := n) (𝕜 := ℂ)).toLinearMap.toContinuousLinearMap
  let E := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  let L := ((quadFormContinuousLinearMap u).comp Matrix.reCLM).comp E.symm.toContinuousLinearMap
  have hCX : MemLp (fun ω => C (X ω)) 2 μ := C.comp_memLp' hX
  have hXC : MemLp (fun ω => E (C (X ω))) 2 μ := E.toContinuousLinearMap.comp_memLp' hCX
  have hZC : MemLp (fun A => E A) 2 γ :=
    E.toContinuousLinearMap.comp_memLp' IsGaussian.memLp_two_id
  have hmX : (∫ ω, E (C (X ω)) ∂μ) = 0 := by
    have h1 : (∫ ω, E (C (X ω)) ∂μ) = E (∫ ω, C (X ω) ∂μ) :=
      E.toContinuousLinearMap.integral_comp_comm (hCX.integrable (by norm_num))
    rw [h1, C.integral_comp_comm (hX.integrable (by norm_num)), hmean, map_zero, map_zero]
  have hmZ : (∫ A, E A ∂γ) = 0 := by
    have h1 : (∫ A, E A ∂γ) = E (∫ A, A ∂γ) :=
      E.toContinuousLinearMap.integral_comp_comm (IsGaussian.integrable_id (μ := γ))
    rw [h1, hγmean, map_zero]
  have hL (A : M) : L (E A) = quadForm (Matrix.reCLM A) u := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, quadFormContinuousLinearMap_apply]
  have hLX (ω : Ω) : L (E (C (X ω))) = quadForm (X ω) u := by
    rw [hL]
    change quadForm (Matrix.reCLM ((X ω).map Complex.ofReal)) u = _
    rw [Matrix.reCLM_map_ofReal]
  have hmatch := covariance_comp_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    hXC hZC (hmX.trans hmZ.symm) hcov L L
  simp only [hLX, hL] at hmatch
  have hiX : MemLp (fun ω => quadForm (X ω) u) 2 μ :=
    (quadFormContinuousLinearMap u).comp_memLp' hX
  have hiZ : MemLp (fun A => quadForm (Matrix.reCLM A) u) 2 γ :=
    ((quadFormContinuousLinearMap u).comp Matrix.reCLM).comp_memLp' IsGaussian.memLp_two_id
  rw [covariance_self hiX.aemeasurable, covariance_self hiZ.aemeasurable] at hmatch
  exact hmatch.symm

open scoped Matrix.Norms.L2Operator in
/-- A covariance-matched centered Gaussian proxy for a real centered matrix
inherits its actual complex weak-variance bound and the dimension-preserving
expected-largest-eigenvalue bound. All full entry covariances are matched;
no additional Gaussian norm or variance estimates are assumed.
Source: Tropp (2026), Section 3.3.1.
atlas: sample-covariance-fourth-moment-lower (partial) -/
theorem quadraticWeakVariance_le_and_integral_lambdaMax_le_of_covariance_eq_real
    [Nonempty n] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℝ) (hX : MemLp X 2 μ) (hmean : (∫ ω, X ω ∂μ) = 0)
    (γ : Measure M) [IsGaussian γ] (hγHerm : ∀ᵐ A ∂γ, A.IsHermitian)
    (hγmean : (∫ A, A ∂γ) = 0)
    (hcov : ∀ i j : J,
      cov[fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) i,
        fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) j; μ] =
      cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; γ])
    (c : NNReal) (hd : 2 ≤ Fintype.card n)
    (hvariance : ∀ u : n → ℝ,
      Var[fun ω => quadForm (X ω) u; μ] ≤ (c : ℝ) * ‖WithLp.toLp 2 u‖ ^ 4) :
    quadraticWeakVariance γ ≤ c ∧
      (∫ A, lambdaMax A ∂γ) ≤ Real.sqrt (12 * (c : ℝ) * Fintype.card n) := by
  have hvar (u : n → ℝ) :
      Var[fun A => quadForm (Matrix.reCLM A) u; γ] ≤ (c : ℝ) * ‖WithLp.toLp 2 u‖ ^ 4 := by
    rw [variance_quadForm_reCLM_gaussian_eq_of_covariance_eq_real μ X hX hmean γ hγmean hcov]
    exact hvariance u
  have hiVar (i j : n) : Var[fun A => (A i j).im; γ] = 0 :=
    im_variance_eq_zero_of_covariance_eq_real μ X γ hcov i j
  have hreal := ae_eq_map_ofReal_reCLM_of_im_variance_eq_zero γ hγmean hiVar
  refine ⟨quadraticWeakVariance_le_of_real_quadratic_variance γ hreal c.coe_nonneg hvar, ?_⟩
  let ρ := γ.map (Matrix.reCLM (m := n) (n := n))
  have hρ := isGaussian_integral_eq_zero_ae_isHermitian_map_reCLM γ hγmean hγHerm
  have hρvar (u : n → ℝ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
      Var[fun A => quadForm A u; ρ] ≤ c := by
    rw [variance_map (by exact (quadFormContinuousLinearMap u).continuous.measurable.aemeasurable)
      Matrix.reCLM.continuous.measurable.aemeasurable]
    change Var[fun A => quadForm (Matrix.reCLM A) u; γ] ≤ c
    simpa only [hu, one_pow, mul_one] using hvar u
  have hnet := integrable_specNorm_and_integral_le_sqrt_gaussian_of_quadratic_variance
    ρ hρ.2.1 hρ.2.2 c hd hρvar
  have hn : (∫ A, specNorm A ∂γ) ≤ Real.sqrt (12 * (c : ℝ) * Fintype.card n) := by
    rw [integral_specNorm_eq_integral_specNorm_map_reCLM_of_im_variance_eq_zero γ hγmean hiVar]
    exact hnet.2
  have hiNorm : Integrable (fun A : M => specNorm A) γ := by
    simpa only [specNorm_eq_norm, id_eq] using (IsGaussian.integrable_id (μ := γ)).norm
  have hiMax := integrable_lambdaMax_of_integrable (IsGaussian.integrable_id (μ := γ)) hγHerm
  exact (integral_mono_ae hiMax hiNorm (hγHerm.mono fun A hA => hA.lambdaMax_le_specNorm)).trans hn

end NLAlib

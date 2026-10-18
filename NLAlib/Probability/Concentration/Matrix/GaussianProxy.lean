import NLAlib.Probability.Concentration.Matrix.GaussianProxyMgf
import NLAlib.Probability.Concentration.Matrix.GaussianTraceSumReplacement
import NLAlib.Probability.Concentration.Matrix.WeakVariance
import NLAlib.Probability.Concentration.Matrix.ExtremeIntegrability
import NLAlib.ForMathlib.Probability.SubGammaOptimization

/-!
# Gaussian-proxy bounds for one-sided independent Hermitian sums

The actual covariance-matched Gaussian trace comparison and its native weak
quadratic variance give the source's expected maximum and sharp upper tail.
The strict event includes every deterministic endpoint; a positive upper
summand bound also permits a non-strict event. Source: Tropp (2026), Theorem 1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

/-- The exact scalar variance budget in Gaussian-proxy eigenvalue comparison,
using the actual supremum of unit quadratic-form variances and the actual
expected largest Gaussian eigenvalue. Source: Tropp (2026), Theorem 1.1. -/
def gaussianProxyVariance (γ : Measure M) (R : ℝ) : ℝ :=
  R * (∫ Z, lambdaMax Z ∂γ) / 3 + quadraticWeakVariance γ

open scoped Matrix.Norms.L2Operator in
/-- The Gaussian-proxy variance budget is nonnegative for a centered
Hermitian Gaussian law and a nonnegative upper summand bound. -/
theorem gaussianProxyVariance_nonneg
    (γ : Measure M) [IsGaussian γ] (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian)
    (hmean : ∫ Z, Z ∂γ = 0) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ gaussianProxyVariance γ R := by
  have hφ := integral_lambdaMax_gaussian_nonneg γ hHerm hmean
    (Real.sqrt_nonneg (quadraticWeakVariance γ))
    (fun u hu => variance_re_quadForm_le_sq_sqrt_quadraticWeakVariance_gaussian γ hu)
  exact add_nonneg (div_nonneg (mul_nonneg hR hφ) (by norm_num))
    (quadraticWeakVariance_nonneg γ)

open scoped Matrix.Norms.L2Operator in
omit [Nonempty n] in
private theorem integrable_traceExp_smul_sum_add_pi_of_upper_bound
    {N : ℕ} (ν : Fin N → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hνHerm : ∀ i, ∀ᵐ W ∂ν i, W.IsHermitian)
    {R θ : ℝ} (hbound : ∀ i, ∀ᵐ W ∂ν i, W ≤ R • (1 : M))
    (D : M) (hD : D.IsHermitian) (hθ : 0 ≤ θ) :
    Integrable (fun W : Fin N → M => traceExp (θ • ((∑ i, W i) + D))) (Measure.pi ν) := by
  have hH : ∀ᵐ W ∂Measure.pi ν, ∀ i, (W i).IsHermitian :=
    ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hνHerm i))
  have hB : ∀ᵐ W ∂Measure.pi ν, ∀ i, W i ≤ R • (1 : M) :=
    ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hbound i))
  have hsumH : ∀ᵐ W ∂Measure.pi ν, (θ • ∑ i, W i).IsHermitian := by
    filter_upwards [hH] with W hW
    have hs : (∑ i, W i).IsHermitian := isSelfAdjoint_sum _ (fun i _ => hW i)
    exact hs.smul (IsSelfAdjoint.all θ)
  have hsumB : ∀ᵐ W ∂Measure.pi ν,
      θ • ∑ i, W i ≤ (θ * ((N : ℝ) * R)) • (1 : M) := by
    filter_upwards [hB] with W hW
    have hs : (∑ i, W i) ≤ ((N : ℝ) * R) • (1 : M) := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hW i)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] using hh
    simpa only [smul_smul] using Matrix.matrix_smul_le_smul_of_nonneg hs hθ
  have hi := integrable_traceExp_add_of_ae_upper_bound (θ • D)
    (hD.smul (IsSelfAdjoint.all θ))
    (show Continuous (fun W : Fin N → M => θ • ∑ i, W i) from by fun_prop).aestronglyMeasurable
    hsumH hsumB
  simpa only [smul_add, add_comm] using hi

open scoped Matrix.Norms.L2Operator in
/-- Actual independent product-law sums satisfy the centered scalar sub-gamma
MGF with their Gaussian proxy's exact weak quadratic variance. The trace
replacement is proved, not assumed; no lower summand bound or negative
exponential moment is imposed. Source: Tropp (2026), Proposition 4.9.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem integrable_exp_mul_lambdaMax_sum_pi_sub_and_integral_le_gaussian_proxy
    {N : ℕ} (ν : Fin N → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ W, W ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ W ∂ν i, W.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ i, ∀ᵐ W ∂ν i, W ≤ R • (1 : M))
    (γ : Measure M) [IsGaussian γ]
    (hγHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hγmean : ∫ Z, Z ∂γ = 0)
    (hγcov : ∀ a b,
      (∑ i, cov[fun W => matrixRealCoordinates W a, fun W => matrixRealCoordinates W b; ν i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ])
    (D : M) (hD : D.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ) (hθR : θ * R < 3) :
    Integrable (fun W : Fin N → M => Real.exp (θ * (lambdaMax ((∑ i, W i) + D) -
      ∫ Z, lambdaMax (D + Z) ∂γ))) (Measure.pi ν) ∧
    (∫ W : Fin N → M, Real.exp (θ * (lambdaMax ((∑ i, W i) + D) -
      ∫ Z, lambdaMax (D + Z) ∂γ)) ∂Measure.pi ν) ≤
      (Fintype.card n : ℝ) * Real.exp
        (gaussianProxyVariance γ R * θ ^ 2 / (2 * (1 - (R / 3) * θ))) := by
  have hsumH : ∀ᵐ W ∂Measure.pi ν, (∑ i, W i).IsHermitian := by
    have hh : ∀ᵐ W ∂Measure.pi ν, ∀ i, (W i).IsHermitian :=
      ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hνHerm i))
    exact hh.mono fun W hW => isSelfAdjoint_sum _ (fun i _ => hW i)
  have htrace := integrable_traceExp_smul_sum_add_pi_of_upper_bound ν hνHerm hbound D hD hθ
  have hcomp := integral_traceExp_add_smul_sum_pi_le_gaussianTraceInflation
    ν hν2 hνmean hνHerm hbound γ hγHerm hγmean hγcov
    (θ • D) (hD.smul (IsSelfAdjoint.all θ)) hθ
  have hcomp' : (∫ W : Fin N → M, traceExp (θ • ((∑ i, W i) + D)) ∂Measure.pi ν) ≤
      ∫ Z, traceExp (θ • D + gaussianTraceInflation R θ • Z) ∂γ := by
    simpa only [smul_add, add_comm] using hcomp
  have h := integrable_exp_mul_lambdaMax_sub_and_integral_le_of_trace_comparison
    (fun W : Fin N → M => ∑ i, W i) (by fun_prop) hsumH D hD γ hγHerm hγmean
    (Real.sqrt_nonneg (quadraticWeakVariance γ))
    (fun u hu => variance_re_quadForm_le_sq_sqrt_quadraticWeakVariance_gaussian γ hu)
    hR hθ hθR htrace hcomp'
  simpa only [Real.sq_sqrt (quadraticWeakVariance_nonneg γ), gaussianProxyVariance, add_comm] using h

open scoped Matrix.Norms.L2Operator in
/-- The expected largest eigenvalue of a one-sided independent Hermitian sum
and its sharp strict upper tail are controlled by any actual centered
Gaussian law with the same full real-entry covariance. Every deterministic
endpoint is included; a positive upper summand bound also permits a non-strict
tail event. Source: Tropp (2026), Theorems 1.1 and 4.1.
atlas: gaussian-proxy-eigenvalue-comparison -/
theorem integral_lambdaMax_sum_pi_le_and_measure_gt_le_gaussian_proxy
    {N : ℕ} (ν : Fin N → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ W, W ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ W ∂ν i, W.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ i, ∀ᵐ W ∂ν i, W ≤ R • (1 : M))
    (γ : Measure M) [IsGaussian γ]
    (hγHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hγmean : ∫ Z, Z ∂γ = 0)
    (hγcov : ∀ a b,
      (∑ i, cov[fun W => matrixRealCoordinates W a, fun W => matrixRealCoordinates W b; ν i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ])
    (D : M) (hD : D.IsHermitian) :
    (∫ W : Fin N → M, lambdaMax ((∑ i, W i) + D) ∂Measure.pi ν) ≤
        (∫ Z, lambdaMax (D + Z) ∂γ) +
          Real.sqrt (2 * gaussianProxyVariance γ R * Real.log (Fintype.card n)) +
          (R / 3) * Real.log (Fintype.card n) ∧
    (∀ s : ℝ, 0 ≤ s →
      (Measure.pi ν).real {W : Fin N → M |
        (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s < lambdaMax ((∑ i, W i) + D)} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) ∧
    (0 < R → ∀ s : ℝ, 0 ≤ s →
      (Measure.pi ν).real {W : Fin N → M |
        (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s ≤ lambdaMax ((∑ i, W i) + D)} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) := by
  have hV := gaussianProxyVariance_nonneg γ hγHerm hγmean hR
  have hc : 0 ≤ R / 3 := div_nonneg hR (by norm_num)
  have hd : 1 ≤ (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
  have hmoment (θ : ℝ) (hθ : 0 ≤ θ) (hdom : (R / 3) * θ < 1) :=
    integrable_exp_mul_lambdaMax_sum_pi_sub_and_integral_le_gaussian_proxy
      ν hν2 hνmean hνHerm hR hbound γ hγHerm hγmean hγcov D hD hθ
      (show θ * R < 3 by nlinarith)
  have hX : Integrable (fun W : Fin N → M => lambdaMax ((∑ i, W i) + D)) (Measure.pi ν) := by
    have hi (i : Fin N) : MemLp (fun W : Fin N → M => matrixRealCoordinates (W i)) 2
        (Measure.pi ν) := by
      simpa only [Function.comp_def] using
        (hν2 i).comp_measurePreserving (measurePreserving_eval ν i)
    have hh (i : Fin N) : ∀ᵐ W ∂Measure.pi ν, (W i).IsHermitian :=
      (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hνHerm i)
    simpa only [one_smul, add_comm] using
      integrable_lambdaMax_add_sum_smul_of_memLp_matrixRealCoordinates D hD (fun _ : Fin N => (1 : ℝ))
        (fun i (W : Fin N → M) => W i) hi hh
  refine ⟨integral_le_sqrt_log_add_of_subgamma_mgf hX hd hV hc
      (fun θ hθ hdom => (hmoment θ hθ hdom).1)
      (fun θ hθ hdom => (hmoment θ hθ hdom).2), ?_, ?_⟩
  · intro s hs
    exact measureReal_gt_sqrt_add_le_of_subgamma_mgf hd hV hc
      (fun θ hθ hdom => (hmoment θ hθ hdom).1)
      (fun θ hθ hdom => (hmoment θ hθ hdom).2) hs
  · intro hRpos s hs
    exact measureReal_ge_sqrt_add_le_of_subgamma_mgf hd hV hc
      (Or.inr (div_pos hRpos (by norm_num)))
      (fun θ hθ hdom => (hmoment θ hθ hdom).1)
      (fun θ hθ hdom => (hmoment θ hθ hdom).2) hs

open scoped Matrix.Norms.L2Operator in
/-- Gaussian-proxy expectation and upper tails for actual independent random
matrices with specified marginal laws. The proxy is an actual centered
Hermitian Gaussian law with the full covariance of the independent sum.
The strict tail includes every zero-parameter endpoint; a positive `R`
also permits the non-strict event. Source: Tropp (2026), Theorem 1.1.
atlas: gaussian-proxy-eigenvalue-comparison -/
theorem integral_lambdaMax_sum_le_and_measure_gt_le_gaussian_proxy_of_hasLaw
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : Fin N → Ω → M) (ν : Fin N → Measure M)
    (hW : ∀ i, HasLaw (W i) (ν i) P) (hind : iIndepFun W P)
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ H, H ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ H ∂ν i, H.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ i, ∀ᵐ H ∂ν i, H ≤ R • (1 : M))
    (γ : Measure M) [IsGaussian γ]
    (hγHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hγmean : ∫ Z, Z ∂γ = 0)
    (hγcov : ∀ a b,
      (∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ])
    (D : M) (hD : D.IsHermitian) :
    (∫ ω, lambdaMax ((∑ i, W i ω) + D) ∂P) ≤
        (∫ Z, lambdaMax (D + Z) ∂γ) +
          Real.sqrt (2 * gaussianProxyVariance γ R * Real.log (Fintype.card n)) +
          (R / 3) * Real.log (Fintype.card n) ∧
    (∀ s : ℝ, 0 ≤ s → P.real {ω |
        (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s < lambdaMax ((∑ i, W i ω) + D)} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) ∧
    (0 < R → ∀ s : ℝ, 0 ≤ s → P.real {ω |
        (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s ≤ lambdaMax ((∑ i, W i ω) + D)} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) := by
  let (i : Fin N) : IsProbabilityMeasure (ν i) :=
    (hW i).isProbabilityMeasure_iff.mp inferInstance
  have hlaw := hind.hasLaw_pi hW
  have hid := hlaw.identDistrib (HasLaw.id (μ := Measure.pi ν))
  have hsumH : ∀ᵐ x ∂Measure.pi ν, (∑ i, x i).IsHermitian := by
    have hh : ∀ᵐ x ∂Measure.pi ν, ∀ i, (x i).IsHermitian :=
      ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := ν)).eventually (hνHerm i))
    exact hh.mono fun x hx => isSelfAdjoint_sum _ (fun i _ => hx i)
  have ho : AEMeasurable (fun x : Fin N → M => lambdaMax ((∑ i, x i) + D)) (Measure.pi ν) := by
    simpa only [add_comm] using aemeasurable_lambdaMax_add_of_ae_isHermitian
      D hD (show Measurable (fun x : Fin N → M => ∑ i, x i) from by fun_prop).aemeasurable hsumH
  have hobs := hid.comp_of_aemeasurable (by rw [hlaw.map_eq]; exact ho)
  simp only [Function.comp_def, id_eq] at hobs
  have h := integral_lambdaMax_sum_pi_le_and_measure_gt_le_gaussian_proxy
    ν hν2 hνmean hνHerm hR hbound γ hγHerm hγmean hγcov D hD
  refine ⟨hobs.integral_eq.trans_le h.1, ?_, ?_⟩
  · intro s hs
    have he : P.real {ω | (∫ Z, lambdaMax (D + Z) ∂γ) +
        Real.sqrt (2 * gaussianProxyVariance γ R * s) + (R / 3) * s < lambdaMax ((∑ i, W i ω) + D)} =
        (Measure.pi ν).real {x | (∫ Z, lambdaMax (D + Z) ∂γ) +
        Real.sqrt (2 * gaussianProxyVariance γ R * s) + (R / 3) * s < lambdaMax ((∑ i, x i) + D)} :=
      congrArg ENNReal.toReal (hobs.measure_mem_eq measurableSet_Ioi)
    exact he.trans_le (h.2.1 s hs)
  · intro hRpos s hs
    have he : P.real {ω | (∫ Z, lambdaMax (D + Z) ∂γ) +
        Real.sqrt (2 * gaussianProxyVariance γ R * s) + (R / 3) * s ≤ lambdaMax ((∑ i, W i ω) + D)} =
        (Measure.pi ν).real {x | (∫ Z, lambdaMax (D + Z) ∂γ) +
        Real.sqrt (2 * gaussianProxyVariance γ R * s) + (R / 3) * s ≤ lambdaMax ((∑ i, x i) + D)} :=
      congrArg ENNReal.toReal (hobs.measure_mem_eq measurableSet_Ici)
    exact he.trans_le (h.2.2 hRpos s hs)

end NLAlib

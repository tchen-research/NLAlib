import NLAlib.Probability.Concentration.Matrix.LaplaceTails
import NLAlib.Probability.Concentration.Matrix.LaplaceExpectations
import NLAlib.Probability.Concentration.Matrix.TraceCgfSubadditivity

/-!
# Theorem 3.6.1 — Master expectation and tail bounds

The four master bounds for an independent sum of Hermitian random matrices
(`integral_lambdaMax_sum_le_log_traceExp_cumulantSum_div`,
`measureReal_lambdaMax_sum_ge_le_exp_mul_traceExp_cumulantSum`,
`log_traceExp_cumulantSum_div_le_integral_lambdaMin_sum`,
`measureReal_lambdaMin_sum_le_le_exp_mul_traceExp_cumulantSum`).

Atlas: `matrix-laplace`. Source: Tropp 2015, *An Introduction to Matrix Concentration
Inequalities*, Theorem 3.6.1, equations (3.6.1–4).
-/
open MeasureTheory ProbabilityTheory

namespace NLAlib

section MasterBounds

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
  [NeZero d] (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) {θ : ℝ}

open scoped Matrix.Norms.L2Operator in
/-- The integrated trace exponential of an independent sum is bounded by `traceExp` of the
cumulant sum, and is positive for `θ ≠ 0`. -/
private lemma integral_traceExp_sum_le (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) (hθ : θ ≠ 0) :
    0 < ∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ ∧
    (∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ) ≤ traceExp (cumulantSum μ X θ) := by
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  have hYExp := integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp
  have hTrInt : Integrable (fun ω => traceExp (θ • ∑ k, X k ω)) μ := by
    exact Complex.reCLM.integrable_comp
      ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hYExp)
  have hTrNonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • ∑ k, X k ω) := by
    filter_upwards [hYHerm] with ω hω
    exact (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).1
  refine ⟨?_, ?_⟩
  · have hPos : ∀ᵐ ω ∂μ, 0 < traceExp (θ • ∑ k, X k ω) := by
      filter_upwards [hYHerm] with ω hω
      rcases lt_or_gt_of_ne hθ with hneg | hpos
      · exact (Real.exp_pos _).trans_le
          ((exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).2.2 hneg)
      · exact (Real.exp_pos _).trans_le
          ((exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).2.1 hpos)
    apply (integral_pos_iff_support_of_nonneg_ae hTrNonneg hTrInt).2
    have hFull : Function.support (fun ω => traceExp (θ • ∑ k, X k ω)) =ᵐ[μ]
        (Set.univ : Set Ω) := by
      filter_upwards [hPos] with ω hω
      apply propext
      change (traceExp (θ • ∑ k, X k ω) ≠ 0) ↔ True
      exact iff_true_intro hω.ne'
    rw [measure_congr hFull]
    simp
  · simpa only [Finset.smul_sum] using
      trace_cgf_subadditivity μ X θ hMeas hHerm hIndep hExp

open scoped Matrix.Norms.L2Operator in
/-- **Master expectation bound for `λmax`** of an independent sum of Hermitian random matrices:
for `θ > 0`, `𝔼 λmax(∑ X k) ≤ log traceExp (cumulantSum μ X θ) / θ`. Tropp 2015, Thm 3.6.1,
eq. (3.6.1).
atlas: matrix-laplace -/
theorem integral_lambdaMax_sum_le_log_traceExp_cumulantSum_div (hθ : 0 < θ)
    (hMeas : ∀ k, Measurable (X k)) (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hInt : ∀ k, Integrable (X k) μ) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (∫ ω, lambdaMax (∑ k, X k ω) ∂μ) ≤ Real.log (traceExp (cumulantSum μ X θ)) / θ := by
  obtain ⟨hpos, hCGF⟩ := integral_traceExp_sum_le μ X hMeas hHerm hIndep hExp hθ.ne'
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  exact (integral_lambdaMax_le_log_integral_traceExp_div μ (fun ω => ∑ k, X k ω) hθ
    (Finset.measurable_sum _ (fun k _ => hMeas k)) hYHerm
    (integrable_finsetSum _ (fun k _ => hInt k))
    (integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp)).trans
    (div_le_div_of_nonneg_right (Real.log_le_log hpos hCGF) hθ.le)

open scoped Matrix.Norms.L2Operator in
/-- **Master tail bound for `λmax`** of an independent sum of Hermitian random matrices: for
`θ > 0`, `P{λmax(∑ X k) ≥ t} ≤ e^{-θt} traceExp (cumulantSum μ X θ)`. Tropp 2015, Thm 3.6.1,
eq. (3.6.3).
atlas: matrix-laplace -/
theorem measureReal_lambdaMax_sum_ge_le_exp_mul_traceExp_cumulantSum (hθ : 0 < θ)
    (hMeas : ∀ k, Measurable (X k)) (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) (t : ℝ) :
    μ.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
      Real.exp (-θ * t) * traceExp (cumulantSum μ X θ) := by
  obtain ⟨-, hCGF⟩ := integral_traceExp_sum_le μ X hMeas hHerm hIndep hExp hθ.ne'
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  exact (measureReal_lambdaMax_ge_le_exp_mul_integral_traceExp μ (fun ω => ∑ k, X k ω) hθ hYHerm
    (integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp) t).trans
    (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)

open scoped Matrix.Norms.L2Operator in
/-- **Master expectation bound for `λmin`** of an independent sum of Hermitian random matrices:
for `θ < 0`, `log traceExp (cumulantSum μ X θ) / θ ≤ 𝔼 λmin(∑ X k)`. Tropp 2015, Thm 3.6.1,
eq. (3.6.2).
atlas: matrix-laplace -/
theorem log_traceExp_cumulantSum_div_le_integral_lambdaMin_sum (hθ : θ < 0)
    (hMeas : ∀ k, Measurable (X k)) (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hInt : ∀ k, Integrable (X k) μ) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    Real.log (traceExp (cumulantSum μ X θ)) / θ ≤ (∫ ω, lambdaMin (∑ k, X k ω) ∂μ) := by
  obtain ⟨hpos, hCGF⟩ := integral_traceExp_sum_le μ X hMeas hHerm hIndep hExp hθ.ne
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  exact (div_le_div_of_nonpos_of_le hθ.le (Real.log_le_log hpos hCGF)).trans
    (log_integral_traceExp_div_le_integral_lambdaMin μ (fun ω => ∑ k, X k ω) hθ
      (Finset.measurable_sum _ (fun k _ => hMeas k)) hYHerm
      (integrable_finsetSum _ (fun k _ => hInt k))
      (integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp))

open scoped Matrix.Norms.L2Operator in
/-- **Master tail bound for `λmin`** of an independent sum of Hermitian random matrices: for
`θ < 0`, `P{λmin(∑ X k) ≤ t} ≤ e^{-θt} traceExp (cumulantSum μ X θ)`. Tropp 2015, Thm 3.6.1,
eq. (3.6.4).
atlas: matrix-laplace -/
theorem measureReal_lambdaMin_sum_le_le_exp_mul_traceExp_cumulantSum (hθ : θ < 0)
    (hMeas : ∀ k, Measurable (X k)) (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) (t : ℝ) :
    μ.real {ω | lambdaMin (∑ k, X k ω) ≤ t} ≤
      Real.exp (-θ * t) * traceExp (cumulantSum μ X θ) := by
  obtain ⟨-, hCGF⟩ := integral_traceExp_sum_le μ X hMeas hHerm hIndep hExp hθ.ne
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  exact (measureReal_lambdaMin_le_le_exp_mul_integral_traceExp μ (fun ω => ∑ k, X k ω) hθ hYHerm
    (integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp) t).trans
    (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)

end MasterBounds

end NLAlib

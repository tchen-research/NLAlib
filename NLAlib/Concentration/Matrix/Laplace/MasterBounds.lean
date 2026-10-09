import NLAlib.Concentration.Matrix.Laplace.LaplaceTails
import NLAlib.Concentration.Matrix.Laplace.LaplaceExpectations
import NLAlib.Concentration.Matrix.Laplace.TraceCgfSubadditivity
import NLAlib.Concentration.Matrix.Laplace.MasterSumExponentialIntegrable
import NLAlib.Concentration.Matrix.Laplace.TailSpectralComparison
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Theorem 3.6.1 — Master expectation and tail bounds

Main declaration: `NLAlib.master_bounds`.

Atlas: `matrix-laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 3.6.1, equations (3.6.1–4), printed pp. 36.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open NLAlib
set_option autoImplicit false

/-- Master bounds for an independent sum of Hermitian random matrices: the expectation and tail of
`λmax` (for `θ > 0`) and of `λmin` (for `θ < 0`) are controlled by `traceExp (cumulantSum μ X θ)`.

Tropp 2015, Thm 3.6.1. Atlas: `matrix-laplace`. Ported from the Prove2me mission *An Introduction
to Matrix Concentration Inequalities, Ch 3*. -/
theorem NLAlib.master_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hInt : ∀ k, Integrable (X k) μ) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (0 < θ →
      (∫ ω, lambdaMax (∑ k, X k ω) ∂μ) ≤
        Real.log (traceExp (cumulantSum μ X θ)) / θ ∧
      ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (∑ k, X k ω)}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) ∧
    (θ < 0 →
      Real.log (traceExp (cumulantSum μ X θ)) / θ ≤
        (∫ ω, lambdaMin (∑ k, X k ω) ∂μ) ∧
      ∀ t : ℝ, (μ {ω | lambdaMin (∑ k, X k ω) ≤ t}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) := by
  have hYMeas : Measurable (fun ω => ∑ k, X k ω) :=
    Finset.measurable_sum _ (fun k _ => hMeas k)
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  have hYInt : Integrable (fun ω => ∑ k, X k ω) μ :=
    integrable_finsetSum _ (fun k _ => hInt k)
  have hYExp := integrable_matrixExp_smul_sum_of_iIndepFun μ X θ hMeas hHerm hIndep hExp
  have hTrInt : Integrable (fun ω => traceExp (θ • ∑ k, X k ω)) μ := by
    exact Complex.reCLM.integrable_comp
      ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hYExp)
  have hTrNonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • ∑ k, X k ω) := by
    filter_upwards [hYHerm] with ω hω
    exact (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).1
  have hTrPos (hθ : θ ≠ 0) : 0 < ∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ := by
    have hPos : ∀ᵐ ω ∂μ, 0 < traceExp (θ • ∑ k, X k ω) := by
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
  have hCGF : (∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ) ≤
      traceExp (cumulantSum μ X θ) := by
    simpa only [Finset.smul_sum] using
      trace_cgf_subadditivity μ X θ hMeas hHerm hIndep hExp
  have hTails := measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le μ (fun ω => ∑ k, X k ω) θ hYMeas hYHerm hYExp
  have hMeans := integral_lambdaMax_le_and_le_integral_lambdaMin μ (fun ω => ∑ k, X k ω) θ
    hYMeas hYHerm hYInt hYExp
  constructor
  · intro hθ
    constructor
    · exact (hMeans.1 hθ).trans (div_le_div_of_nonneg_right
        (Real.log_le_log (hTrPos hθ.ne') hCGF) hθ.le)
    · intro t
      exact (hTails.1 hθ t).trans (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)
  · intro hθ
    constructor
    · exact (div_le_div_of_nonpos_of_le hθ.le
        (Real.log_le_log (hTrPos hθ.ne) hCGF)).trans (hMeans.2 hθ)
    · intro t
      exact (hTails.2 hθ t).trans (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)

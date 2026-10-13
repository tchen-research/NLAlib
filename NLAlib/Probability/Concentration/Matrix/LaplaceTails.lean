import NLAlib.Probability.Concentration.Basic.MatrixStatistics
import NLAlib.Matrix.Functions.TraceExpBounds
import Mathlib.Tactic.Positivity

/-!
# Proposition 3.2.1 — Tail bounds for eigenvalues

Main declaration: `NLAlib.measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le`.

Atlas: `matrix-laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 3.2.1, printed pp. 32–33.
-/
open MeasureTheory ProbabilityTheory

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
private lemma integrable_re_trace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (Z : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hZ : Integrable Z μ) : Integrable (fun ω => (Matrix.trace (Z ω)).re) μ := by
  exact Complex.reCLM.integrable_comp
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hZ)

open scoped Matrix.Norms.L2Operator in
private lemma measureReal_le_exp_neg_mul_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (s : Set Ω)
    (a : ℝ) (hF : Integrable F μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hs : ∀ᵐ ω ∂μ, ω ∈ s → Real.exp a ≤ F ω) :
    μ.real s ≤ Real.exp (-a) * ∫ ω, F ω ∂μ := by
  have hsub : μ s ≤ μ {ω | Real.exp a ≤ F ω} :=
    measure_mono_ae hs
  have hreal : μ.real s ≤ μ.real {ω | Real.exp a ≤ F ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hpos hF (Real.exp a)
  have hmul : Real.exp a * μ.real s ≤ ∫ ω, F ω ∂μ :=
    (mul_le_mul_of_nonneg_left hreal (Real.exp_pos a).le).trans hmarkov
  calc
    μ.real s = Real.exp (-a) * (Real.exp a * μ.real s) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le

end NLAlib

open NLAlib

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Laplace transform, upper tail**: for `θ > 0`,
`P{λmax(Y) ≥ t} ≤ e^{-θt} 𝔼 traceExp (θ • Y)`. Tropp 2015, Prop. 3.2.1.
atlas: matrix-laplace -/
theorem NLAlib.measureReal_lambdaMax_ge_le_exp_mul_integral_traceExp {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) (t : ℝ) :
    μ.real {ω | t ≤ lambdaMax (Y ω)} ≤
      Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ) := by
  have hInt : Integrable (fun ω => traceExp (θ • Y ω)) μ :=
    integrable_re_trace μ _ hExp
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • Y ω) := by
    filter_upwards [hHerm] with ω hω
    exact (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).1
  have h := measureReal_le_exp_neg_mul_integral μ (fun ω => traceExp (θ • Y ω))
    {ω | t ≤ lambdaMax (Y ω)} (θ * t) hInt hnonneg ?_
  · simpa only [neg_mul] using h
  · filter_upwards [hHerm] with ω hω
    intro ht
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hθ.le)).trans
      ((exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).2.1 hθ)

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Laplace transform, lower tail**: for `θ < 0`,
`P{λmin(Y) ≤ t} ≤ e^{-θt} 𝔼 traceExp (θ • Y)`. Tropp 2015, Prop. 3.2.1.
atlas: matrix-laplace -/
theorem NLAlib.measureReal_lambdaMin_le_le_exp_mul_integral_traceExp {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) {θ : ℝ} (hθ : θ < 0)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) (t : ℝ) :
    μ.real {ω | lambdaMin (Y ω) ≤ t} ≤
      Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ) := by
  have hInt : Integrable (fun ω => traceExp (θ • Y ω)) μ :=
    integrable_re_trace μ _ hExp
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • Y ω) := by
    filter_upwards [hHerm] with ω hω
    exact (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).1
  have h := measureReal_le_exp_neg_mul_integral μ (fun ω => traceExp (θ • Y ω))
    {ω | lambdaMin (Y ω) ≤ t} (θ * t) hInt hnonneg ?_
  · simpa only [neg_mul] using h
  · filter_upwards [hHerm] with ω hω
    intro ht
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht hθ.le)).trans
      ((exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ hω θ).2.2 hθ)

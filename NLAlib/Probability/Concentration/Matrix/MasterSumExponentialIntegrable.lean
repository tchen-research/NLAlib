import NLAlib.Probability.Concentration.Basic.MatrixStatistics
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Probability.Independence.Integration
import NLAlib.Matrix.Functions.ExpLogPosDef
import NLAlib.Matrix.Functions.TraceExpBounds

/-!
# Exponential integrability of an independent Hermitian sum

Main declaration: `NLAlib.integrable_matrixExp_smul_sum_of_iIndepFun`.

Atlas: `matrix-laplace` (regularity lemma).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for the proof of Theorem 3.6.1, printed p. 36; Section 2.2.1, printed p. 25, states the standing regularity convention. This is explicit analytic groundwork, not a separately numbered theorem in the book.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder
open NLAlib
set_option autoImplicit false

/-- For independent Hermitian random matrices with integrable `matrixExp (θ • X k)`, the exponential
`matrixExp (θ • ∑ k, X k)` of the sum is integrable.

Tropp 2015, regularity lemma for Thm 3.6.1. Atlas: `matrix-laplace`. Ported from the Prove2me
mission *An Introduction to Matrix Concentration Inequalities, Ch 3*.

Auxiliary; not a numbered result in the source. -/
theorem NLAlib.integrable_matrixExp_smul_sum_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    Integrable (fun ω => matrixExp (θ • ∑ k, X k ω)) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let f : Matrix (Fin d) (Fin d) ℂ → ℝ := fun A => 1 + ‖matrixExp (θ • A)‖
  have hfcont : Continuous f := by
    dsimp [f, matrixExp]
    fun_prop
  have hfmap (k : Fin N) : Integrable f (μ.map (X k)) := by
    apply (integrable_map_measure hfcont.aestronglyMeasurable (hMeas k).aemeasurable).2
    exact (integrable_const 1).add (hExp k).norm
  have hprod : Integrable (fun ω => ∏ k, f (X k ω)) μ := by
    have hpi := Integrable.fintype_prod hfmap
    rw [← hIndep.map_fun_eq_pi_map (fun k => (hMeas k).aemeasurable)] at hpi
    have hpc : Continuous (fun x : Fin N → Matrix (Fin d) (Fin d) ℂ => ∏ i, f (x i)) :=
      continuous_finsetProd _ (fun i _ => hfcont.comp (continuous_apply i))
    exact (integrable_map_measure hpc.aestronglyMeasurable
      (measurable_pi_lambda _ hMeas).aemeasurable).1 hpi
  apply hprod.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
      (f := fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A))
      (by dsimp [matrixExp]; fun_prop) |>.comp_measurable
    exact Finset.measurable_sum _ (fun k _ => hMeas k)
  · filter_upwards [ae_all_iff.2 hHerm] with ω hω
    simpa only [Finset.smul_sum] using
      norm_matrixExp_sum_le_prod (fun k => θ • X k ω) (fun k => (hω k).smul (isSelfAdjoint_iff.mpr rfl))

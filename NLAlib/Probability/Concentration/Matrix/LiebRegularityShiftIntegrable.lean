import NLAlib.Probability.Concentration.Basic.MatrixStatistics
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.FinCases
import NLAlib.Matrix.Functions.ExpLogPosDef
import NLAlib.Matrix.Functions.TraceExpBounds

/-!
# Exponential integrability survives a fixed Hermitian shift

Main declaration: `NLAlib.integrable_matrixExp_add_and_traceExp_add`.

Atlas: `matrix-laplace` (regularity lemma).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for Corollary 3.4.2 and the proof of Lemma 3.5.1, printed pp. 35–36; standing regularity convention in Section 2.2.1, printed p. 25.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder
open NLAlib

/-- If `matrixExp X` is integrable for a Hermitian random matrix `X`, then so are `matrixExp (H + X)`
and `traceExp (H + X)` for every fixed Hermitian `H`.

Tropp 2015, regularity lemma for Corollary 3.4.2 and Lemma 3.5.1. Atlas: `matrix-laplace`. Ported
from the Prove2me mission *An Introduction to Matrix Concentration Inequalities, Ch 3*.

Auxiliary; not a numbered result in the source. -/
theorem NLAlib.integrable_matrixExp_add_and_traceExp_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    Integrable (fun ω => matrixExp (H + X ω)) μ ∧
      Integrable (fun ω => traceExp (H + X ω)) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hInt : Integrable (fun ω => matrixExp (H + X ω)) μ := by
    have hBoundInt : Integrable (fun ω =>
        (1 + ‖matrixExp H‖) * (1 + ‖matrixExp (X ω)‖)) μ :=
      ((integrable_const 1).add hExp.norm).const_mul _
    apply hBoundInt.mono' ?_ ?_
    · have hc : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (H + A)) := by
        dsimp [matrixExp]
        fun_prop
      exact hc.aestronglyMeasurable.comp_measurable hMeas
    · filter_upwards [hHerm] with ω hω
      have hh : ∀ k : Fin 2, (![H, X ω] k).IsHermitian := by
        intro k
        fin_cases k
        · exact hH
        · exact hω
      simpa [Fin.sum_univ_two, Fin.prod_univ_two] using
        norm_matrixExp_sum_le_prod ![H, X ω] hh
  exact ⟨hInt, Complex.reCLM.integrable_comp
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hInt)⟩

import NLAlib.Concentration.Matrix.OperatorConvexity.LiebConcavity
import NLAlib.Concentration.Matrix.Laplace.LiebJensen
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import NLAlib.Concentration.Matrix.Laplace.LiebIntegralPosDef
import NLAlib.Concentration.Matrix.Laplace.LiebRegularityShiftIntegrable
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Corollary 3.4.2 — Probabilistic Lieb inequality

Main declaration: `NLAlib.integral_traceExp_add_le_traceExp_add_matrixLog`.

Atlas: `matrix-laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Corollary 3.4.2, printed p. 35.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace NLAlib

/-- The Lieb trace function is continuous on the actual positive-definite cone.
Source: Tropp 2015, Corollary 3.4.2; operator rederivations `eq:condlieb`.
Reusable regularity for atlas `matrix-laplace` and `matrix-freedman`; promoted unchanged
from the proof-local helper of probabilistic Lieb. -/
theorem continuousOn_traceExp_add_matrixLog {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) :
    ContinuousOn (fun A => traceExp (H + matrixLog A))
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hl : ContinuousOn (matrixLog : Matrix (Fin d) (Fin d) ℂ → _)
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} :=
    CFC.continuousOn_log.mono (fun A hA => ⟨hA.isHermitian, hA.isUnit⟩)
  have he : ContinuousOn (fun A => matrixExp (H + matrixLog A))
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} :=
    NormedSpace.exp_continuous.comp_continuousOn (continuousOn_const.add hl)
  exact Complex.continuous_re.comp_continuousOn
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.continuous.comp_continuousOn he)

end NLAlib

open NLAlib

/-- Probabilistic Lieb inequality: `𝔼 traceExp (H + X) ≤ traceExp (H + matrixLog (𝔼 matrixExp X))` for
fixed Hermitian `H` and a Hermitian random matrix `X`.

Tropp 2015, Cor. 3.4.2. Atlas: `matrix-laplace`. Ported from the Prove2me mission *An Introduction
to Matrix Concentration Inequalities, Ch 3*. -/
theorem NLAlib.integral_traceExp_add_le_traceExp_add_matrixLog {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    (∫ ω, traceExp (H + X ω) ∂μ) ≤
      traceExp (H + matrixLog (∫ ω, matrixExp (X ω) ∂μ)) := by
  have hp : ∀ᵐ ω ∂μ, (matrixExp (X ω)).PosDef :=
    hHerm.mono fun ω hω => (posDef_matrixExp_and_matrixLog_matrixExp (X ω) hω).1
  have hm := posDef_integral_of_ae_posDef μ (fun ω => matrixExp (X ω)) hExp hp
  have heq : (fun ω => traceExp (H + matrixLog (matrixExp (X ω)))) =ᵐ[μ]
      (fun ω => traceExp (H + X ω)) :=
    hHerm.mono fun ω hω => by dsimp only; rw [(posDef_matrixExp_and_matrixLog_matrixExp (X ω) hω).2]
  have hi := (integrable_matrixExp_add_and_traceExp_add μ H hH X hMeas hHerm hExp).2
  rw [← integral_congr_ae heq]
  exact ConcaveOn.le_map_integral_of_integral_mem μ _ _ _ (lieb_concavity H hH)
    (continuousOn_traceExp_add_matrixLog H) hp hExp (hi.congr heq.symm) hm

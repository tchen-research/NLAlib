import NLAlib.ForMathlib.MeasureTheory.ConditionalJensen
import NLAlib.Concentration.Matrix.OperatorConvexity.LiebReindex

/-!
# Actual conditional Lieb inequality for a fixed Hermitian offset

The proved nonclosed-domain conditional Jensen theorem applies directly to the actual
positive-definite exponential and its actual conditional mean. Mean positivity and
integrability are explicit foundations to be derived in the martingale application.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

/-- Conditional Lieb for a fixed Hermitian offset, using the actual conditional mean of
the matrix exponential. This is a genuine conditional Jensen theorem, not the existing
unconditional inequality or an assumed conditional-mgf certificate. Its conditional-mean
positivity and trace integrability premises are supplied by the subsequent martingale bounds.
Source: Tropp 2011, Freedman's inequality; operator rederivations `eq:condlieb`.
atlas: matrix-freedman (partial) -/
theorem condExp_traceExp_add_le_traceExp_add_matrixLog_of_ae_posDef_condExp
    {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (X : Ω → Matrix n n ℂ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ)
    (hTrace : Integrable (fun ω => traceExp (H + X ω)) μ)
    (hmean : ∀ᵐ ω ∂μ, (μ[(fun ω => matrixExp (X ω)) | m] ω).PosDef) :
    μ[(fun ω => traceExp (H + X ω)) | m] ≤ᵐ[μ]
      fun ω => traceExp (H + matrixLog (μ[(fun ω => matrixExp (X ω)) | m] ω)) := by
  have hpos : ∀ᵐ ω ∂μ, (matrixExp (X ω)).PosDef :=
    hHerm.mono fun ω hω => (posDef_matrixExp_and_matrixLog_matrixExp_finite _ hω).1
  have heq : (fun ω => traceExp (H + matrixLog (matrixExp (X ω)))) =ᵐ[μ]
      (fun ω => traceExp (H + X ω)) := by
    filter_upwards [hHerm] with ω hω
    rw [(posDef_matrixExp_and_matrixLog_matrixExp_finite _ hω).2]
  have hJ := ConcaveOn.condExp_map_le_of_condExp_mem hm (lieb_concavity_finite H hH)
    (continuousOn_traceExp_add_matrixLog_finite H) hpos hExp (hTrace.congr heq.symm) hmean
  filter_upwards [hJ, condExp_congr_ae heq] with ω hω hEq
  rw [← hEq]
  exact hω

end NLAlib

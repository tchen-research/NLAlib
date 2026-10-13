import NLAlib.Matrix.OperatorTheory.LiebConcavity
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The Lieb trace function on any finite index type

`A ↦ traceExp (H + matrixLog A)` on the positive-definite cone: continuity
(`continuousOn_traceExp_add_matrixLog`, any finite index type). Its concavity is
`lieb_concavity` (OperatorTheory/LiebConcavity, any finite index type), re-exported by the import.

Tropp 2015, Theorem 3.4.1 and Corollary 3.4.2. Moved from
`NLAlib.Probability.Concentration.Matrix.{ProbabilisticLieb,LiebReindex}` (dedup round
2026-10-12). Atlas: `matrix-laplace`, `matrix-freedman` (partial).
-/

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

/-- The Lieb trace function is continuous on the actual positive-definite cone.
Source: Tropp 2015, Corollary 3.4.2; operator rederivations `eq:condlieb`.
Reusable regularity for atlas `matrix-laplace` and `matrix-freedman`; promoted unchanged
from the proof-local helper of probabilistic Lieb. -/
theorem continuousOn_traceExp_add_matrixLog {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℂ) :
    ContinuousOn (fun A => traceExp (H + matrixLog A))
      {A : Matrix d d ℂ | A.PosDef} := by
  let : NormedAlgebra ℚ (Matrix d d ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hl : ContinuousOn (matrixLog : Matrix d d ℂ → _)
      {A : Matrix d d ℂ | A.PosDef} :=
    CFC.continuousOn_log.mono (fun A hA => ⟨hA.isHermitian, hA.isUnit⟩)
  have he : ContinuousOn (fun A => matrixExp (H + matrixLog A))
      {A : Matrix d d ℂ | A.PosDef} :=
    NormedSpace.exp_continuous.comp_continuousOn (continuousOn_const.add hl)
  exact Complex.continuous_re.comp_continuousOn
    ((Matrix.traceLinearMap d ℂ ℂ).toContinuousLinearMap.continuous.comp_continuousOn he)

end NLAlib

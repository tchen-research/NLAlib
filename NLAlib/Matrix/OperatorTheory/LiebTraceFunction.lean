import NLAlib.Matrix.OperatorTheory.LiebConcavity
import NLAlib.Matrix.Functions.UnitaryCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The Lieb trace function on any finite index type

`A ↦ traceExp (H + matrixLog A)` on the positive-definite cone: continuity
(`continuousOn_traceExp_add_matrixLog`, any finite index type) and concavity transported from
`lieb_concavity` (stated over `Fin d`) to every nonempty finite index type
(`lieb_concavity_finite`).

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

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing Lieb concavity theorem on the actual positive-definite cone, transported
to every nonempty finite index type.
Source: Tropp 2015, Theorem 3.4.1; exact finite-label transport of `lieb_concavity`.
atlas: matrix-freedman (partial) -/
theorem lieb_concavity_finite [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} (fun A => traceExp (H + matrixLog A)) := by
  let e := Fintype.equivFin n
  let E := reindexStarAlgEquiv e
  let L := (Matrix.reindexLinearEquiv ℝ ℂ e e).toLinearMap
  have h := (lieb_concavity (E H) (hH.reindex e)).comp_linearMap L
  have hdomain : L ⁻¹' {A | A.PosDef} = {A : Matrix n n ℂ | A.PosDef} := by
    ext A
    exact posDef_reindex_iff e A
  rw [hdomain] at h
  apply h.congr
  intro A hA
  change traceExp (E H + matrixLog (E A)) = traceExp (H + matrixLog A)
  have hlog : matrixLog (E A) = E (matrixLog A) := matrixLog_reindex_of_isHermitian e A hA.1
  rw [hlog]
  have ha : E H + E (matrixLog A) = E (H + matrixLog A) := (map_add E _ _).symm
  rw [ha]
  exact traceExp_reindex e _

end NLAlib

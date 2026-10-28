import NLAlib.Solvers.LeastSquares.SketchAndSolve
import NLAlib.Matrix.Measurability.GramPseudoinverse

/-!
# Measurability of the native sketch-and-solve estimator

The actual Moore--Penrose definition is measurable at every input rank.
No chosen eigenvectors or a full-rank restriction is needed.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p s : Type*} [Fintype m] [Fintype n] [Fintype s]

/-- The actual minimum-norm sketched estimator is measurable as a function
of the sketch, over both real and complex scalars. -/
theorem measurable_sketchAndSolve [DecidableEq s] [DecidableEq n]
    (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    Measurable (fun S : Matrix s m 𝕜 => sketchAndSolve A S B) := by
  unfold sketchAndSolve
  exact (measurable_moorePenroseInverse.comp (measurable_id.matrix_mul measurable_const)).matrix_mul
    (measurable_id.matrix_mul measurable_const)

open scoped Matrix.Norms.L2Operator in
/-- The native squared residual is measurable even on deficient sketches. -/
theorem measurable_frobSq_sketchAndSolve_residual [Fintype p] [DecidableEq s] [DecidableEq n]
    (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    Measurable (fun S : Matrix s m 𝕜 => frobSq (B-A*sketchAndSolve A S B)) := by
  apply measurable_frobSq.comp
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  exact measurable_const.sub ((Matrix.measurable_entry i j).comp
    (measurable_const.matrix_mul (measurable_sketchAndSolve A B)))

end NLAlib

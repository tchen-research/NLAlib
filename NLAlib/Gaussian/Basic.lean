import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Standard Gaussian matrices

`NLAlib.gaussianMatrix p m` is the law of a `p × m` matrix with i.i.d. `N(0,1)` entries, as the
product measure on `Fin p → Fin m → ℝ`; `Matrix.of` is the matrix view. This is the convention of
the Gaussian Random Matrices series and of the LRA project, so results port without change.

Atlas: `gaussian-matrix-def`. Bridge lemmas to Mathlib's `stdGaussian` are a planned target.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- Law of a `p × m` matrix with independent standard Gaussian entries. -/
def gaussianMatrix (p m : ℕ) : Measure (Fin p → Fin m → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

instance isProbabilityMeasure_gaussianMatrix (p m : ℕ) :
    IsProbabilityMeasure (gaussianMatrix p m) := by
  unfold gaussianMatrix; infer_instance

end NLAlib

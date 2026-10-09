import TroppMatrixConcentration.Defs.Probability
import TroppMatrixConcentration.Defs.Dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace TroppMatrixConcentration

def intrinsicDimension {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace A).re / spectralNorm A

def traceFunction {d : Type*} [Fintype d] [DecidableEq d]
    (φ : ℝ → ℝ) (A : Matrix d d ℂ) : ℝ := (Matrix.trace (cfc φ A)).re

end TroppMatrixConcentration

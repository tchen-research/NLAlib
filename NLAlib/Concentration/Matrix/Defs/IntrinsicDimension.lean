import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.Dilation
import Mathlib.Analysis.Convex.Function

/-!
# Intrinsic dimension

The intrinsic dimension of a matrix and trace functions.

Atlas: `intrinsic-dimension`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

/-- The intrinsic dimension `tr A / ‖A‖`. Tropp 2015, Def. 7.1.1. Atlas: `intrinsic-dimension`. -/
def intrinsicDimension {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace A).re / spectralNorm A

/-- The trace function `re (tr φ(A))`, with `φ(A)` from the continuous functional calculus. Tropp
2015, §7.4. -/
def traceFunction {d : Type*} [Fintype d] [DecidableEq d]
    (φ : ℝ → ℝ) (A : Matrix d d ℂ) : ℝ := (Matrix.trace (cfc φ A)).re

end NLAlib

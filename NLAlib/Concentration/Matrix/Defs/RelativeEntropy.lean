import NLAlib.Concentration.Matrix.Defs.Spectral
import Mathlib.Analysis.Convex.Function

/-!
# Matrix functions, relative entropy, operator convexity

The standard matrix function, matrix relative entropy, operator convexity on an interval, and the matrix perspective.

Atlas: `operator-monotone-convex`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

/-- The standard matrix function `f(A)`, defined by the continuous functional calculus. Tropp 2015,
§2.1.6. -/
def matrixFunction {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ := cfc f A

/-- The matrix relative entropy `D(A; H) = re tr (A (log A - log H) - (A - H))`. Tropp 2015, eq.
(8.1.1). Atlas: `operator-monotone-convex`. -/
def relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A H : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H))).re

/-- `f` is operator convex on the convex set `I`: `f (t A + (1-t) H) ≼ t f(A) + (1-t) f(H)` for all
Hermitian `A`, `H` of every size with spectra in `I`. Tropp 2015, Def. 8.4.6. Atlas:
`operator-monotone-convex`. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ I ∧ ∀ (d : ℕ) (_ : NeZero d) (A H : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → H.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ H ⊆ I →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      LoewnerLE (matrixFunction f (t • A + (1 - t) • H))
        (t • matrixFunction f A + (1 - t) • matrixFunction f H)

/-- The matrix perspective `A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}`. Tropp 2015, Def. 8.6.1. Atlas:
`operator-monotone-convex`. -/
def matrixPerspective {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A H : Matrix d d ℂ) : Matrix d d ℂ :=
  let S := matrixFunction Real.sqrt A
  let R := matrixFunction (fun x => (Real.sqrt x)⁻¹) A
  S * matrixFunction f (R * H * R) * S

end NLAlib

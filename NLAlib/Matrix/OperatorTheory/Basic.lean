import NLAlib.Matrix.Functions.ExpLog

/-!
# Matrix functions, relative entropy, operator convexity

Matrix relative entropy, operator convexity on an interval, and the matrix perspective. The standard
matrix function `f(A)` (Tropp 2015, §2.1.6) is Mathlib's continuous functional calculus `cfc f A`.

Atlas: `operator-monotone-convex`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open scoped MatrixOrder

noncomputable section
namespace NLAlib

/-- The matrix relative entropy `D(A; H) = re tr (A (log A - log H) - (A - H))`. Tropp 2015, eq.
(8.1.1). Atlas: `operator-monotone-convex`.
atlas: operator-monotone-convex -/
def relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A H : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H))).re

/-- `f` is operator convex on the convex set `I`: `f (t A + (1-t) H) ≼ t f(A) + (1-t) f(H)` for all
Hermitian `A`, `H` of every size with spectra in `I`. Tropp 2015, Def. 8.4.6. Atlas:
`operator-monotone-convex`.
atlas: operator-monotone-convex -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ I ∧ ∀ (d : ℕ) (_ : NeZero d) (A H : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → H.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ H ⊆ I →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      (cfc f (t • A + (1 - t) • H)) ≤
        (t • cfc f A + (1 - t) • cfc f H)

/-- The matrix perspective `A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}`. Tropp 2015, Def. 8.6.1. Atlas:
`operator-monotone-convex`.
atlas: operator-monotone-convex -/
def matrixPerspective {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A H : Matrix d d ℂ) : Matrix d d ℂ :=
  let S := cfc Real.sqrt A
  let R := cfc (fun x => (Real.sqrt x)⁻¹) A
  S * cfc f (R * H * R) * S

end NLAlib

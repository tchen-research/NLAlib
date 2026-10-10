import NLAlib.Concentration.Matrix.Defs.RelativeEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Proposition 8.4.4 — Logarithm is operator monotone

Main declaration: `NLAlib.matrixLog_le_matrixLog`.

Atlas: `operator-monotone-convex`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.4.4, printed p. 128.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NLAlib
set_option autoImplicit false

/-- The logarithm is operator monotone: `A ≼ H` implies `matrixLog A ≼ matrixLog H` for positive
definite `A`, `H`.

Tropp 2015, Prop. 8.4.4. Atlas: `operator-monotone-convex`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 8*.
atlas: operator-monotone-convex -/
theorem NLAlib.matrixLog_le_matrixLog {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef)
    (hAH : LoewnerLE A H) :
    LoewnerLE (matrixLog A) (matrixLog H) := by
  exact CFC.log_monotoneOn hA.isStrictlyPositive hH.isStrictlyPositive hAH

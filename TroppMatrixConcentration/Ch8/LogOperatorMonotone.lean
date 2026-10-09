import TroppMatrixConcentration.Defs.Ch8Entropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Proposition 8.4.4 — Logarithm is operator monotone

Lean name: `TroppMatrixConcentration.ch8_log_operator_monotone`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.4.4, printed p. 128.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem TroppMatrixConcentration.ch8_log_operator_monotone {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef)
    (hAH : loewnerLE A H) :
    loewnerLE (matrixLog A) (matrixLog H) := by
  exact CFC.log_monotoneOn hA.isStrictlyPositive hH.isStrictlyPositive hAH

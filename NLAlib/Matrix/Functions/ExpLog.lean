import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Spectral vocabulary for complex matrices

Extreme eigenvalues, matrix exponential and logarithm, and trace exponential on `Matrix d d ℂ`.
The spectral norm is Mathlib's `‖A‖` under `open scoped Matrix.Norms.L2Operator`, and the
Loewner order is Mathlib's `≤` from `Mathlib.Analysis.Matrix.Order` (`open scoped MatrixOrder`;
`Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`).

Atlas: `loewner-order`; used by `matrix-laplace` and every later chapter.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

/-- The largest real spectral value `sSup (spectrum ℝ A)`; the largest eigenvalue of a Hermitian
matrix. Tropp 2015, §2.1.
atlas: matrix-calculus-def -/
def lambdaMax {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sSup (spectrum ℝ A)

/-- The smallest real spectral value `sInf (spectrum ℝ A)`; the smallest eigenvalue of a Hermitian
matrix. Tropp 2015, §2.1.
atlas: matrix-calculus-def -/
def lambdaMin {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sInf (spectrum ℝ A)

/-- The matrix exponential. Tropp 2015, §2.1.11.
atlas: matrix-calculus-def -/
def matrixExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := NormedSpace.exp A

/-- The matrix logarithm, defined by the continuous functional calculus. Tropp 2015, §2.1.12.
atlas: matrix-calculus-def -/
def matrixLog {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := cfc Real.log A

/-- `matrixLog` is Mathlib's `CFC.log` (both are `cfc Real.log`), by `rfl`. Mathlib's `CFC.log`
API (`CFC.log_exp`, `CFC.log_le_log`, `CFC.log_monotoneOn`, `CFC.log_smul`, …) applies to
`matrixLog` through this bridge. -/
theorem matrixLog_eq_log {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    matrixLog A = CFC.log A :=
  rfl

/-- The trace exponential `re (tr (matrixExp A))`. Tropp 2015, §3.1.
atlas: matrix-calculus-def -/
def traceExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace (matrixExp A)).re

end NLAlib

import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
/-!
# Hermitian exponential is positive definite and logarithm is its inverse

Main declaration: `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`.

Atlas: `loewner-order` (matrix exponential and logarithm); supports `matrix-laplace`.

Stated over `ℂ`: the proof uses `CFC.log_exp` and `CFC.real_exp_eq_normedSpace_exp`, which need
`NormedAlgebra ℝ (Matrix d d ℂ)` (the C*-algebra structure); the generic-`𝕜` CFC instance of
Mathlib does not provide it. Tropp 2015, §2.1.11–12, eq. (2.1.17).
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NLAlib

/-- The exponential of a Hermitian matrix is positive definite and `matrixLog` inverts it: `(matrixExp
A).PosDef ∧ matrixLog (matrixExp A) = A`, on any finite index type (including the empty one).
The second conjunct is Mathlib's `CFC.log_exp` (`matrixLog = CFC.log`, `matrixLog_eq_log`).

Tropp 2015, §2.1.11–12, eq. (2.1.17).
atlas: matrix-calculus-def -/
theorem NLAlib.posDef_matrixExp_and_matrixLog_matrixExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by
  constructor
  · rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
    apply Matrix.IsStrictlyPositive.posDef
    exact (cfc_isStrictlyPositive_iff Real.exp A (by fun_prop) hA.isSelfAdjoint).mpr
      (fun x _ => Real.exp_pos x)
  · exact CFC.log_exp A hA.isSelfAdjoint

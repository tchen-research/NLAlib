import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import NLAlib.Matrix.Spectral.Core

/-!
# Matrix exponential, logarithm and trace exponential

`matrixExp`, `matrixLog` and `traceExp` on `Matrix d d 𝕜` for `[RCLike 𝕜]`: the exponential is
Mathlib's `NormedSpace.exp` in the C*-algebra `Matrix d d 𝕜` (spectral norm,
`open scoped Matrix.Norms.L2Operator`), the logarithm is the continuous functional calculus
`cfc Real.log`, and the Loewner order is Mathlib's `≤` from `Mathlib.Analysis.Matrix.Order`.
The extreme spectral values `lambdaMax`/`lambdaMin` are in `Matrix/Spectral/Core.lean`.

Tropp 2015, §2.1.11–§2.1.12 and §3.1. Atlas: `matrix-calculus-def`; used by `matrix-laplace`
and the matrix concentration inequalities.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] [DecidableEq d]

/-- The **matrix exponential** `exp A = ∑ Aᵏ/k!` (Mathlib's `NormedSpace.exp`). Tropp 2015,
§2.1.11.
atlas: matrix-calculus-def -/
def matrixExp (A : Matrix d d 𝕜) : Matrix d d 𝕜 := NormedSpace.exp A

/-- The **matrix logarithm** `cfc Real.log A`, by the continuous functional calculus: the
inverse of `matrixExp` on positive definite matrices (`CFC.log_exp`). For a matrix with a
non-positive spectrum the value is Mathlib's `cfc` junk (`0` off the self-adjoint matrices).
Tropp 2015, §2.1.12.
atlas: matrix-calculus-def -/
def matrixLog (A : Matrix d d 𝕜) : Matrix d d 𝕜 := cfc Real.log A

/-- `matrixLog` is Mathlib's `CFC.log` (both are `cfc Real.log`), by `rfl`. Mathlib's `CFC.log`
API (`CFC.log_exp`, `CFC.log_le_log`, `CFC.log_monotoneOn`, `CFC.log_smul`, …) applies to
`matrixLog` through this bridge (stated over `ℂ`, where `Matrix d d ℂ` is a C*-algebra). -/
theorem matrixLog_eq_log (A : Matrix d d ℂ) : matrixLog A = CFC.log A :=
  rfl

/-- The **trace exponential** `re (tr (exp A))`. Tropp 2015, §3.1.
atlas: matrix-calculus-def -/
def traceExp (A : Matrix d d 𝕜) : ℝ := RCLike.re (Matrix.trace (matrixExp A))

/-- Over `ℂ` the trace exponential is the real part of the trace, as a `Complex.re`. -/
theorem traceExp_complex (A : Matrix d d ℂ) :
    traceExp A = (Matrix.trace (matrixExp A)).re :=
  rfl

end NLAlib

import NLAlib.Matrix.Functions.ExpLog
import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Random-matrix statistics

Variance statistics, the cumulant sum of the matrix Laplace method, and the Bernstein tail.

Atlas: `matrix-laplace`, `matrix-bernstein`. Source: Tropp 2015, *An Introduction to Matrix
Concentration Inequalities*, §§2.2, 3.5, 6.1.
-/

open MeasureTheory

noncomputable section
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The matrix variance statistic of a rectangular random matrix: `max ‖𝔼 Z Zᴴ‖ ‖𝔼 Zᴴ Z‖` (spectral
norms); `0` when the second moments are not integrable (junk value of the Bochner integral).
Tropp 2015, eq. (2.2.9).
atlas: matrix-bernstein -/
def rectSecondMoment {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (μ : Measure Ω) (Z : Ω → Matrix m n ℂ) : ℝ :=
  max (specNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (specNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ))

open scoped Matrix.Norms.L2Operator in
/-- The matrix variance statistic of a Hermitian random matrix: the spectral norm `‖𝔼 Y²‖`; `0` when
`Y²` is not integrable. Tropp 2015, eq. (2.2.4).
atlas: matrix-bernstein -/
def hermitianSecondMoment {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] (μ : Measure Ω) (Y : Ω → Matrix d d ℂ) : ℝ :=
  specNorm (∫ ω, Y ω ^ 2 ∂μ)

open scoped Matrix.Norms.L2Operator in
/-- The sum of matrix cumulant generating functions `∑ k, matrixLog (𝔼 matrixExp (θ • X k))`; a
non-integrable summand contributes `matrixLog 0 = 0`. Tropp 2015, §3.5.
atlas: matrix-laplace -/
def cumulantSum {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] {N : ℕ}
    (μ : Measure Ω) (X : Fin N → Ω → Matrix d d ℂ) (θ : ℝ) : Matrix d d ℂ :=
  ∑ k, matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ)

open scoped Matrix.Norms.L2Operator in
/-- The matrix Bernstein tail `d · exp (-(t²/2)/(v + L t/3))`, defined piecewise in the degenerate
case `v + L t/3 = 0` (`d` at `t = 0`, `0` otherwise). Tropp 2015, Thm 6.1.1.
atlas: matrix-bernstein -/
def bernsteinTail (dimension : ℕ) (v L t : ℝ) : ℝ :=
  if v + L * t / 3 = 0 then
    if t = 0 then (dimension : ℝ) else 0
  else (dimension : ℝ) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3))

end NLAlib

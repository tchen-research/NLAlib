import NLAlib.Concentration.Matrix.Defs.Spectral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Random-matrix statistics

Borel structure on complex matrices, variance statistics, the cumulant sum of the matrix Laplace method, and the Bernstein tail.

Atlas: `matrix-laplace`, `matrix-bernstein`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLAlib

/-- The Borel σ-algebra on complex matrices (for the norm topology), used to state measurability of
random matrices. -/
instance matrixMeasurableSpace {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  borel (Matrix m n ℂ)

/-- Complex matrices with `matrixMeasurableSpace` form a Borel space. -/
instance matrixBorelSpace {m n : Type*} : BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

/-- The matrix variance statistic of a rectangular random matrix: `max ‖𝔼 Z Zᴴ‖ ‖𝔼 Zᴴ Z‖`. Tropp 2015,
eq. (2.2.9). -/
def rectSecondMoment {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (μ : Measure Ω) (Z : Ω → Matrix m n ℂ) : ℝ :=
  max (spectralNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (spectralNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ))

/-- The matrix variance statistic of a Hermitian random matrix: `‖𝔼 Y²‖`. Tropp 2015, eq. (2.2.4). -/
def hermitianSecondMoment {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] (μ : Measure Ω) (Y : Ω → Matrix d d ℂ) : ℝ :=
  spectralNorm (∫ ω, Y ω ^ 2 ∂μ)

/-- The sum of matrix cumulant generating functions `∑ k, matrixLog (𝔼 matrixExp (θ • X k))`. Tropp
2015, §3.5. Atlas: `matrix-laplace`. -/
def cumulantSum {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] {N : ℕ}
    (μ : Measure Ω) (X : Fin N → Ω → Matrix d d ℂ) (θ : ℝ) : Matrix d d ℂ :=
  ∑ k, matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ)

/-- The matrix Bernstein tail `d · exp (-(t²/2)/(v + L t/3))`, defined piecewise in the degenerate
case `v + L t/3 = 0`. Tropp 2015, Thm 6.1.1. Atlas: `matrix-bernstein`. -/
def bernsteinTail (dimension : ℕ) (v L t : ℝ) : ℝ :=
  if v + L * t / 3 = 0 then
    if t = 0 then (dimension : ℝ) else 0
  else (dimension : ℝ) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3))

end NLAlib

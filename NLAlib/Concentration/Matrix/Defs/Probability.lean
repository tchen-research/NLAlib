import NLAlib.Concentration.Matrix.Defs.Spectral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLAlib

instance matrixMeasurableSpace {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  borel (Matrix m n ℂ)

instance matrixBorelSpace {m n : Type*} : BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

def rectSecondMoment {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (μ : Measure Ω) (Z : Ω → Matrix m n ℂ) : ℝ :=
  max (spectralNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (spectralNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ))

def hermitianSecondMoment {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] (μ : Measure Ω) (Y : Ω → Matrix d d ℂ) : ℝ :=
  spectralNorm (∫ ω, Y ω ^ 2 ∂μ)

def cumulantSum {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] {N : ℕ}
    (μ : Measure Ω) (X : Fin N → Ω → Matrix d d ℂ) (θ : ℝ) : Matrix d d ℂ :=
  ∑ k, matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ)

def bernsteinTail (dimension : ℕ) (v L t : ℝ) : ℝ :=
  if v + L * t / 3 = 0 then
    if t = 0 then (dimension : ℝ) else 0
  else (dimension : ℝ) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3))

end NLAlib

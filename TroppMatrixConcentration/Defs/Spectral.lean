import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace TroppMatrixConcentration

def spectralNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ := ‖A‖

def lambdaMax {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sSup (spectrum ℝ A)

def lambdaMin {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sInf (spectrum ℝ A)

def matrixExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := NormedSpace.exp A

def matrixLog {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := cfc Real.log A

def traceExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace (matrixExp A)).re

def loewnerLE {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) : Prop := (B - A).PosSemidef

end TroppMatrixConcentration

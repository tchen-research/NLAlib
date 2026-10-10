import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Spectral vocabulary for complex matrices

Spectral norm, extreme eigenvalues, matrix exponential and logarithm, trace exponential, and the Loewner order on `Matrix d d ℂ`.

Atlas: `loewner-order`; used by `matrix-laplace` and every later chapter.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

/-- The spectral norm (ℓ₂ operator norm) of a complex matrix. Tropp 2015, §2.1.
atlas: matrix-calculus-def -/
def spectralNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ := ‖A‖

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

/-- The trace exponential `re (tr (matrixExp A))`. Tropp 2015, §3.1.
atlas: matrix-calculus-def -/
def traceExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace (matrixExp A)).re

/-- The Loewner (semidefinite) order: `LoewnerLE A B` iff `B - A` is positive semidefinite. Tropp
2015, §2.1.5. Atlas: `loewner-order`.
atlas: matrix-calculus-def -/
def LoewnerLE {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) : Prop := (B - A).PosSemidef

end NLAlib

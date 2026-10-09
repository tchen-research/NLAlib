import NLAlib.Concentration.Matrix.Defs.Spectral
import Mathlib.Analysis.Convex.Function

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

def ch8_matrixFunction {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ := cfc f A

def ch8_relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A H : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H))).re

def ch8_operatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ I ∧ ∀ (d : ℕ) (_ : NeZero d) (A H : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → H.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ H ⊆ I →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      loewnerLE (ch8_matrixFunction f (t • A + (1 - t) • H))
        (t • ch8_matrixFunction f A + (1 - t) • ch8_matrixFunction f H)

def ch8_perspective {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A H : Matrix d d ℂ) : Matrix d d ℂ :=
  let S := ch8_matrixFunction Real.sqrt A
  let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
  S * ch8_matrixFunction f (R * H * R) * S

end NLAlib

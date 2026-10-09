import TroppMatrixConcentration.Defs.Ch8Entropy
import Mathlib.Logic.Equiv.Fin.Basic

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix
noncomputable section
namespace TroppMatrixConcentration

def ch8_joint_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

def ch8_joint_right {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ H.transpose).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

def ch8_joint_vec {d : ℕ} (i : Fin (d * d)) : ℂ :=
  if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 then 1 else 0

def ch8_joint_eval {d : ℕ} (M : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : ℝ :=
  (star ch8_joint_vec ⬝ᵥ (M *ᵥ ch8_joint_vec)).re

end TroppMatrixConcentration

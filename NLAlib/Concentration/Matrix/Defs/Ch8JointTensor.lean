import NLAlib.Concentration.Matrix.Defs.Ch8Entropy
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensor representation for relative entropy

The Kronecker factors `A ⊗ I`, `I ⊗ Hᵀ` on `Fin (d * d)`, the vectorized identity, and the quadratic form it defines.

Atlas: `operator-monotone-convex`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix
noncomputable section
namespace NLAlib

/-- The left tensor factor `A ⊗ I`, reindexed to `Fin (d * d)`. Tropp 2015, §8.8. -/
def jointTensorLeft {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The right tensor factor `I ⊗ Hᵀ`, reindexed to `Fin (d * d)`. Tropp 2015, §8.8. -/
def jointTensorRight {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ H.transpose).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The vectorized identity matrix `vec I` on `Fin (d * d)`. Tropp 2015, §8.8. -/
def jointTensorVec {d : ℕ} (i : Fin (d * d)) : ℂ :=
  if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 then 1 else 0

/-- The quadratic form `re ⟨vec I, M vec I⟩`. Tropp 2015, §8.8. -/
def jointTensorEval {d : ℕ} (M : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : ℝ :=
  (star jointTensorVec ⬝ᵥ (M *ᵥ jointTensorVec)).re

end NLAlib

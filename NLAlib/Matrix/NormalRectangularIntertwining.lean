import NLAlib.Matrix.NormalIntertwining
import Mathlib.Data.Matrix.Block

/-!
# Rectangular Fuglede–Putnam for complex normal matrices

Embedding a rectangular intertwiner as one off-diagonal block reduces the
compatible unequal-size result to the square C⋆-algebra theorem.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- Rectangular intertwining of complex normal matrices is equivalent to
intertwining their adjoints. Source: Horn–Johnson (2013), Theorem 2.5.15;
the two normal matrices may have different sizes, including empty shapes.
atlas: normal-matrices (partial) -/
theorem mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal_rectangular
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {X : Matrix m n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B) :
    A * X = X * B ↔ Aᴴ * X = X * Bᴴ := by
  let M : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks A 0 0 B
  let N : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks 0 X 0 0
  have hM : M * Mᴴ = Mᴴ * M := by
    simp only [M, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, hA, hB]
  have h := mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal
    (A := M) (B := M) (X := N) hM hM
  simpa only [M, N, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj, true_and, and_self, and_true] using h

end NLAlib

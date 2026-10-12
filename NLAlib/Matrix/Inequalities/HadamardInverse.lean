import NLAlib.Matrix.Inequalities.HadamardOrder
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Inverse inequalities for Hadamard products

A Hadamard product is a diagonal principal block of the Kronecker product.
Inverse compression supplies the inverse bound, while the Schur product of
two inverse Gram blocks supplies the identity lower bound.
Source: Horn--Johnson (2013), Theorems 7.7.14 and 7.7.17;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Selecting equal row and column tensor indices from a Kronecker product
gives the Hadamard product. Horn--Johnson (2013), Section 7.5;
helper for the inverse compression inequality. -/
theorem submatrix_kronecker_diagonal (A B : Matrix n n ℝ) :
    (A ⊗ₖ B).submatrix (fun i => (i, i)) (fun i => (i, i)) = A ⊙ B := by
  ext i j
  rfl

/-- Inversion of a Hadamard product is bounded above by the Hadamard product
of the inverses of two positive definite matrices. Empty dimensions are
included. Horn--Johnson (2013), Corollary 7.7.14.
atlas: schur-product-inequalities (partial) -/
theorem inv_hadamard_le_hadamard_inv {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A ⊙ B)⁻¹ ≤ A⁻¹ ⊙ B⁻¹ := by
  have h := inv_submatrix_le_submatrix_inv (hA.kronecker hB) (fun i : n => (i, i))
    (fun _ _ he => congrArg Prod.fst he)
  simpa only [submatrix_kronecker_diagonal, Matrix.inv_kronecker] using h

/-- A positive definite matrix Hadamard-multiplied by its inverse dominates
identity in Loewner order. Horn--Johnson (2013), Theorem 7.7.17.
atlas: schur-product-inequalities (partial) -/
theorem one_le_hadamard_inv {A : Matrix n n ℝ} (hA : A.PosDef) : 1 ≤ A ⊙ A⁻¹ := by
  let : Invertible A := hA.isUnit.invertible
  have h1 : (fromBlocks A 1 1 A⁻¹).PosSemidef := by
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
      fromBlocks_inverse_gram_posSemidef hA (1 : Matrix n n ℝ)
  have h2 : (fromBlocks A⁻¹ 1 1 A).PosSemidef := by
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_inv_of_invertible] using
      fromBlocks_inverse_gram_posSemidef hA.inv (1 : Matrix n n ℝ)
  have he : fromBlocks A 1 1 A⁻¹ ⊙ fromBlocks A⁻¹ 1 1 A =
      fromBlocks (A ⊙ A⁻¹) 1 1 (A ⊙ A⁻¹) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.hadamard_apply, Matrix.one_apply, mul_comm]
  have h := h1.hadamard h2
  rw [he] at h
  exact (posSemidef_equal_diagonal_fromBlocks_iff_le (hA.posSemidef.hadamard hA.inv.posSemidef)
    Matrix.PosSemidef.one).mp h

end NLAlib

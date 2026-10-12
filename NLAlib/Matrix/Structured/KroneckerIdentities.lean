import NLAlib.Matrix.Basic.MoorePenrose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Frobenius and Moore–Penrose identities for Kronecker products

These identities need no invertibility or rank assumptions and allow arbitrary
finite row and column types, including empty types. Source: Horn–Johnson 1991,
Section 4.2. Atlas: `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix Kronecker

namespace NLAlib

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Squared Frobenius norms multiply under the Kronecker product.
Horn–Johnson 1991, Section 4.2; all finite rectangular shapes, including empty ones.
atlas: kronecker-spectral (partial) -/
theorem frobSq_kronecker (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    frobSq (A ⊗ₖ B) = frobSq A * frobSq B := by
  simp only [frobSq_eq_sum_sq, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, mul_pow]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Frobenius norms multiply under the Kronecker product.
Horn–Johnson 1991, Section 4.2; no nonzero or nonempty assumptions.
atlas: kronecker-spectral (partial) -/
theorem frobNorm_kronecker (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    frobNorm (A ⊗ₖ B) = frobNorm A * frobNorm B := by
  rw [frobNorm, frobNorm, frobNorm, frobSq_kronecker, Real.sqrt_mul (frobSq_nonneg A)]

/-- Tensoring two matrices and their Moore–Penrose inverses preserves all four
Penrose equations. Horn–Johnson 1991, Section 4.2; rank deficient matrices are allowed.
-/
theorem IsMoorePenroseInverse.kronecker {A : Matrix m n ℝ} {A' : Matrix n m ℝ}
    {B : Matrix p q ℝ} {B' : Matrix q p ℝ}
    (hA : IsMoorePenroseInverse A A') (hB : IsMoorePenroseInverse B B') :
    IsMoorePenroseInverse (A ⊗ₖ B) (A' ⊗ₖ B') := by
  constructor
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hA.mul_mul_eq, hB.mul_mul_eq]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hA.inv_mul_inv_eq, hB.inv_mul_inv_eq]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.kroneckerMap_transpose,
      hA.transpose_mul_eq, hB.transpose_mul_eq]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.kroneckerMap_transpose,
      hA.transpose_inv_mul_eq, hB.transpose_inv_mul_eq]

/-- The Moore–Penrose inverse of a Kronecker product is the product of the two
Moore–Penrose inverses. Horn–Johnson 1991, Section 4.2; arbitrary finite rectangular
matrices and all zero singular values are included.
atlas: kronecker-spectral (partial) -/
theorem moorePenroseInverse_kronecker (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    moorePenroseInverse (A ⊗ₖ B) = moorePenroseInverse A ⊗ₖ moorePenroseInverse B :=
  (isMoorePenroseInverse _).unique ((isMoorePenroseInverse A).kronecker
    (isMoorePenroseInverse B))

end NLAlib

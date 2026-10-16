import NLAlib.Matrix.Basic.Orthonormal
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Realification of complex matrices

The real matrix of a complex-linear map in real and imaginary coordinates is
`[[Re A,-Im A],[Im A,Re A]]`. This construction preserves multiplication and
adjoints and doubles the real trace. It supports transporting real Schatten
inequalities and orthogonal Gaussian invariance to complex matrices.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n p : Type*}

/-- The real matrix of a complex matrix acting on real and imaginary parts. -/
def matrixRealification (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (fun i j => (A i j).re) (fun i j => -(A i j).im)
    (fun i j => (A i j).im) (fun i j => (A i j).re)

/-- Realification preserves addition. -/
@[simp] theorem matrixRealification_add (A B : Matrix m n ℂ) :
    matrixRealification (A+B) = matrixRealification A + matrixRealification B := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification sends zero to zero. -/
@[simp] theorem matrixRealification_zero : matrixRealification (0 : Matrix m n ℂ) = 0 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification preserves negation. -/
@[simp] theorem matrixRealification_neg (A : Matrix m n ℂ) :
    matrixRealification (-A) = -matrixRealification A := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification preserves subtraction. -/
@[simp] theorem matrixRealification_sub (A B : Matrix m n ℂ) :
    matrixRealification (A-B) = matrixRealification A - matrixRealification B := by
  rw [sub_eq_add_neg,matrixRealification_add,matrixRealification_neg,←sub_eq_add_neg]

/-- Realification commutes with real scalar multiplication. -/
@[simp] theorem matrixRealification_smul (r : ℝ) (A : Matrix m n ℂ) :
    matrixRealification (r • A) = r • matrixRealification A := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm] <;> ring

/-- Realification sends the complex identity matrix to the real identity. -/
@[simp] theorem matrixRealification_one [DecidableEq n] :
    matrixRealification (1 : Matrix n n ℂ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, Matrix.one_apply, apply_ite]

/-- The real matrix of a product is the product of the real matrices. -/
@[simp] theorem matrixRealification_mul [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    matrixRealification (A*B) = matrixRealification A * matrixRealification B := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, matrixRealification, Matrix.mul_apply, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, mul_neg, neg_mul, add_comm, sub_eq_add_neg]

/-- The complex adjoint becomes real transposition under realification. -/
@[simp] theorem matrixRealification_conjTranspose (A : Matrix m n ℂ) :
    matrixRealification Aᴴ = (matrixRealification A)ᵀ := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, Matrix.conjTranspose_apply]

/-- A unitary matrix realifies to a real matrix with orthonormal columns. -/
theorem HasOrthonormalCols.realification [Fintype m] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : HasOrthonormalCols A) :
    HasOrthonormalCols (matrixRealification A) := by
  change (matrixRealification A)ᴴ * matrixRealification A = 1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,←matrixRealification_conjTranspose,
    ←matrixRealification_mul,hA.conjTranspose_mul_self,matrixRealification_one]

/-- The real trace of a realification is twice the real part of the complex
trace, including the zero-dimensional case. -/
theorem trace_matrixRealification [Fintype n] (A : Matrix n n ℂ) :
    (matrixRealification A).trace = 2 * A.trace.re := by
  simp [Matrix.fromBlocks, matrixRealification, Matrix.trace, Fintype.sum_sum_type, map_sum]
  ring

/-- Realification commutes with simultaneous relabeling of the two coordinate
copies on each side. -/
theorem matrixRealification_reindex {r s : Type*} (A : Matrix m n ℂ)
    (em : m ≃ r) (en : n ≃ s) :
    matrixRealification (A.reindex em en) =
      (matrixRealification A).reindex (Equiv.sumCongr em em) (Equiv.sumCongr en en) := by
  ext i j
  cases i <;> cases j <;> simp [matrixRealification, Matrix.fromBlocks, Matrix.reindex_apply]

/-- Realification of a real diagonal is the diagonal with every real entry
repeated on its real and imaginary coordinate copies. -/
theorem matrixRealification_diagonal_ofReal [DecidableEq n] (d : n → ℝ) :
    matrixRealification (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (Sum.elim d d) := by
  ext i j
  cases i <;> cases j <;>
    simp [matrixRealification, Matrix.fromBlocks, Matrix.diagonal_apply, apply_ite] <;>
      split_ifs <;> simp_all

end NLAlib

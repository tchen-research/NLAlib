import NLAlib.Matrix.Functions.PolynomialIntertwining
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Polynomial triangular block differences

Finite insertion sums compute polynomial evaluation on triangular matrices.
Source: matrix-toolkit derivations, F16--F18; helpers for
`matrix-function-block-divided-differences`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {𝕜 m n o : Type*} [CommRing 𝕜]
variable [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- The upper triangular two-block matrix. -/
def upperBlockTwo (A : Matrix m m 𝕜) (H : Matrix m n 𝕜) (B : Matrix n n 𝕜) :=
  Matrix.fromBlocks A H 0 B

/-- The finite one-insertion sum for a monomial. -/
def monomialBlockDifference (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  ∑ j ∈ Finset.range k, A ^ (k.pred - j) * H * B ^ j

theorem monomialBlockDifference_succ (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) :
    monomialBlockDifference A B H (k + 1) =
      A ^ k * H + monomialBlockDifference A B H k * B := by
  simp only [monomialBlockDifference, Nat.pred_succ]
  rw [Finset.sum_range_succ', add_comm]
  simp only [tsub_zero, pow_zero, Matrix.mul_one, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : k - (j + 1) = k.pred - j := by
    simp [Nat.pred_eq_sub_one, Nat.sub_sub, Nat.add_comm]
  rw [he, pow_succ]
  simp only [Matrix.mul_assoc]

/-- Actual powers of triangular matrices have the insertion sum as their upper block. -/
theorem upperBlockTwo_pow (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) (k : ℕ) :
    upperBlockTwo A H B ^ k =
      Matrix.fromBlocks (A ^ k) (monomialBlockDifference A B H k) 0 (B ^ k) := by
  induction k with
  | zero => simp [upperBlockTwo, monomialBlockDifference, Matrix.fromBlocks_one]
  | succ k hk =>
    rw [pow_succ, hk, upperBlockTwo, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ,
      monomialBlockDifference_succ]

/-- The first polynomial block difference, written as a finite insertion sum. -/
def polynomialBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • monomialBlockDifference A B H k

/-- Polynomial evaluation on an actual triangular matrix. -/
theorem aeval_upperBlockTwo (p : 𝕜[X]) (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) :
    aeval (upperBlockTwo A H B) p =
      Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B H) 0 (aeval B p) := by
  simp only [aeval_eq_sum_range, upperBlockTwo_pow, polynomialBlockDifference]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.sum_apply, Matrix.smul_apply]

/-- The ordered second polynomial difference: two insertions in their given order. -/
def polynomialSecondBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜) :
    Matrix m o 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k, monomialBlockDifference A B G (k.pred - j) * H * C ^ j

/-- A three-block triangular matrix with a zero direct first-to-third block. -/
def upperBlockThree (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) : Matrix ((m ⊕ n) ⊕ o) ((m ⊕ n) ⊕ o) 𝕜 :=
  upperBlockTwo (upperBlockTwo A G B) (Matrix.fromRows 0 H) C

theorem polynomialBlockDifference_upperBlockTwo (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    polynomialBlockDifference p (upperBlockTwo A G B) C (Matrix.fromRows 0 H) =
      Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
        (polynomialBlockDifference p B C H) := by
  simp only [polynomialBlockDifference, monomialBlockDifference, upperBlockTwo_pow,
    Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero, zero_add,
    Matrix.fromRows_mul]
  ext i j
  rcases i with i | i <;>
    simp only [polynomialSecondBlockDifference, monomialBlockDifference,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, smul_eq_mul]

/-- The ordered second difference is the actual first-to-third block of the
polynomial of a three-block triangular matrix. -/
theorem aeval_upperBlockThree (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    aeval (upperBlockThree A G B H C) p =
      Matrix.fromBlocks
        (Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B G) 0 (aeval B p))
        (Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
          (polynomialBlockDifference p B C H)) 0 (aeval C p) := by
  simp only [upperBlockThree, aeval_upperBlockTwo, polynomialBlockDifference_upperBlockTwo]

end NLAlib

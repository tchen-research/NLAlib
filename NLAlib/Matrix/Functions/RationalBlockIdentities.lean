import NLAlib.Matrix.Functions.RationalBlocks

/-!
# Exact finite differences of rational matrix functions

Rectangular intertwiners prove the two ordered second difference identities
without commutativity or diagonalizability assumptions. Source: F18.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

/-- The exact first finite-difference formula for a rational matrix function.
Source: F18.
atlas: matrix-function-block-divided-differences (partial) -/
theorem rationalMatrixEval_sub (P Q : 𝕜[X]) (A B : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q A - rationalMatrixEval P Q B =
      rationalBlockDifference P Q A B (A - B) := by
  let M := upperBlockTwo A (A - B) B
  let S : Matrix n (n ⊕ n) 𝕜 := Matrix.fromCols 1 1
  have hi : A * S = S * M := by
    simp [S, M, upperBlockTwo, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi hA
    (isUnit_aeval_upperBlockTwo Q A B (A - B) hA hB)
  rw [show M = upperBlockTwo A (A - B) B from rfl,
    rationalMatrixEval_upperBlockTwo P Q A B (A - B) hA hB] at hf
  have he := congrArg Matrix.toCols₂ hf
  simp [S, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at he
  exact (sub_eq_iff_eq_add).mpr he

/-- Changing the right base point produces the ordered second block difference.
Source: F18.
atlas: matrix-function-block-divided-differences (partial) -/
theorem rationalBlockDifference_sub_right (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A B H - rationalBlockDifference P Q A C H =
      rationalSecondBlockDifference P Q A B C H (B - C) := by
  let M := upperBlockThree A H B (B - C) C
  let S : Matrix ((n ⊕ n) ⊕ n) (n ⊕ n) 𝕜 :=
    Matrix.fromRows 1 (Matrix.fromCols 0 (-1))
  have hi : M * S = S * upperBlockTwo A H C := by
    simp only [M, S, upperBlockThree, upperBlockTwo, Matrix.fromBlocks_mul_fromRows,
      Matrix.fromRows_mul, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols,
      Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul]
    ext ((i | i) | i) (j | j) <;> simp
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi
    (isUnit_aeval_upperBlockThree Q A B C H (B - C) hA hB hC)
    (isUnit_aeval_upperBlockTwo Q A C H hA hC)
  rw [show M = upperBlockThree A H B (B - C) C from rfl,
    rationalMatrixEval_upperBlockThree P Q A B C H (B - C) hA hB hC,
    rationalMatrixEval_upperBlockTwo P Q A C H hA hC] at hf
  simp only [S, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.mul_one,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul] at hf
  ext i j
  have he := congrArg (fun D => D (Sum.inl (Sum.inl i)) (Sum.inr j)) hf
  simp at he
  simp only [Matrix.sub_apply]
  have he' : rationalBlockDifference P Q A B H i j -
      rationalSecondBlockDifference P Q A B C H (B - C) i j =
      rationalBlockDifference P Q A C H i j := by simpa only [sub_eq_add_neg] using he
  exact sub_eq_of_eq_add (by simpa only [add_comm] using sub_eq_iff_eq_add.mp he')

/-- Changing the left base point produces the other ordered second difference.
Source: F18.
atlas: matrix-function-block-divided-differences (partial) -/
theorem rationalBlockDifference_sub_left (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A C H - rationalBlockDifference P Q B C H =
      rationalSecondBlockDifference P Q A B C (A - B) H := by
  let M := upperBlockThree A (A - B) B H C
  let S : Matrix (n ⊕ n) ((n ⊕ n) ⊕ n) 𝕜 :=
    Matrix.fromCols (Matrix.fromRows (Matrix.fromCols 1 1) 0)
      (Matrix.fromRows 0 1)
  have hi : upperBlockTwo A H C * S = S * M := by
    simp only [M, S, upperBlockThree, upperBlockTwo, Matrix.fromBlocks_mul_fromRows,
      Matrix.fromRows_mul, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero]
    ext (i | i) ((j | j) | j) <;> simp
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi
    (isUnit_aeval_upperBlockTwo Q A C H hA hC)
    (isUnit_aeval_upperBlockThree Q A B C (A - B) H hA hB hC)
  rw [show M = upperBlockThree A (A - B) B H C from rfl,
    rationalMatrixEval_upperBlockThree P Q A B C (A - B) H hA hB hC,
    rationalMatrixEval_upperBlockTwo P Q A C H hA hC] at hf
  simp only [S, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows] at hf
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero] at hf
  ext i j
  have he := congrArg (fun D => D (Sum.inl i) (Sum.inr j)) hf
  simp at he
  simp only [Matrix.sub_apply]
  exact (sub_eq_iff_eq_add).mpr he

end NLAlib

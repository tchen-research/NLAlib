import NLAlib.Matrix.Functions.PolynomialBlocks

/-!
# Rational triangular block calculus

Rational evaluation means `P(A) Q(A)⁻¹` in the full matrix algebra.
Diagonal denominator invertibility suffices for all triangular evaluations.
Source: matrix-toolkit derivations, F16--F18.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {𝕜 m n o : Type*} [Field 𝕜]
variable [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- Rational functional calculus on the nonsingular-denominator domain. -/
def rationalMatrixEval (P Q : 𝕜[X]) (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  aeval A P * (aeval A Q)⁻¹

/-- The first rational block difference, with its explicit finite formula. -/
def rationalBlockDifference (P Q : 𝕜[X]) (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  (polynomialBlockDifference P A B H -
    rationalMatrixEval P Q A * polynomialBlockDifference Q A B H) * (aeval B Q)⁻¹

/-- The ordered second rational block difference, obtained by triangular inversion. -/
def rationalSecondBlockDifference (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜) :
    Matrix m o 𝕜 :=
  (polynomialSecondBlockDifference P A B C G H -
    rationalMatrixEval P Q A * polynomialSecondBlockDifference Q A B C G H -
    rationalBlockDifference P Q A B G * polynomialBlockDifference Q B C H) * (aeval C Q)⁻¹

theorem isUnit_aeval_upperBlockTwo (Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (H : Matrix m n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    IsUnit (aeval (upperBlockTwo A H B) Q) := by
  rw [aeval_upperBlockTwo]
  exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA, hB⟩

theorem isUnit_aeval_upperBlockThree (Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    IsUnit (aeval (upperBlockThree A G B H C) Q) :=
  isUnit_aeval_upperBlockTwo Q _ _ _ (isUnit_aeval_upperBlockTwo Q A B G hA hB) hC

/-- The first difference is exactly the upper block of the rational function
of the actual triangular matrix. Source: F16--F17.
atlas: matrix-function-block-divided-differences (partial) -/
theorem rationalMatrixEval_upperBlockTwo (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (H : Matrix m n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q (upperBlockTwo A H B) =
      Matrix.fromBlocks (rationalMatrixEval P Q A) (rationalBlockDifference P Q A B H)
        0 (rationalMatrixEval P Q B) := by
  unfold rationalMatrixEval
  rw [aeval_upperBlockTwo, aeval_upperBlockTwo,
    Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ ⟨fun _ => hB, fun _ => hA⟩,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  simp [rationalBlockDifference, rationalMatrixEval, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- The ordered second difference is exactly the first-to-third block.
Only the three diagonal denominator evaluations need be invertible.
Source: F16--F17.
atlas: matrix-function-block-divided-differences (partial) -/
theorem rationalMatrixEval_upperBlockThree (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalMatrixEval P Q (upperBlockThree A G B H C) =
      Matrix.fromBlocks
        (Matrix.fromBlocks (rationalMatrixEval P Q A) (rationalBlockDifference P Q A B G)
          0 (rationalMatrixEval P Q B))
        (Matrix.fromRows (rationalSecondBlockDifference P Q A B C G H)
          (rationalBlockDifference P Q B C H)) 0 (rationalMatrixEval P Q C) := by
  rw [upperBlockThree, rationalMatrixEval_upperBlockTwo P Q _ _ _
    (isUnit_aeval_upperBlockTwo Q A B G hA hB) hC,
    rationalMatrixEval_upperBlockTwo P Q A B G hA hB]
  congr 1
  unfold rationalBlockDifference
  rw [polynomialBlockDifference_upperBlockTwo, polynomialBlockDifference_upperBlockTwo,
    rationalMatrixEval_upperBlockTwo P Q A B G hA hB,
    Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul, zero_add]
  have hsub (D₁ D₂ : Matrix m o 𝕜) (E₁ E₂ : Matrix n o 𝕜) :
      Matrix.fromRows D₁ E₁ - Matrix.fromRows D₂ E₂ =
        Matrix.fromRows (D₁ - D₂) (E₁ - E₂) := by
    ext (i | i) j <;> simp
  rw [hsub, Matrix.fromRows_mul]
  congr 1
  simp only [rationalSecondBlockDifference, sub_sub]

/-- Rational evaluation preserves rectangular intertwining, provided the two
denominators are invertible. -/
theorem rationalMatrixEval_mul_eq_mul_rationalMatrixEval (P Q : 𝕜[X])
    {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {S : Matrix m n 𝕜}
    (h : A * S = S * B) (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q A * S = S * rationalMatrixEval P Q B := by
  have hQ := aeval_mul_eq_mul_aeval_of_mul_eq h Q
  have hP := aeval_mul_eq_mul_aeval_of_mul_eq h P
  have hAd := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hBd := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hi : (aeval A Q)⁻¹ * S = S * (aeval B Q)⁻¹ := by
    calc
      _ = (aeval A Q)⁻¹ * S * (aeval B Q) * (aeval B Q)⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd]
      _ = (aeval A Q)⁻¹ * (aeval A Q * S) * (aeval B Q)⁻¹ := by rw [hQ]; simp only [Matrix.mul_assoc]
      _ = S * (aeval B Q)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAd, Matrix.one_mul]
  simp only [rationalMatrixEval, Matrix.mul_assoc]
  rw [hi, ← Matrix.mul_assoc, hP, Matrix.mul_assoc]

end NLAlib

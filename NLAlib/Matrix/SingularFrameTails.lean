import NLAlib.Matrix.SingularFrames

/-!
# Matched SVD tails in complementary ambient coordinates

The tail removes the chosen leading left and right singular spaces. Its action
on complementary residuals is the projected action of the original matrix.
Source: Wedin (1972), Section 3; supports `wedin-sin-theta`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
namespace IsSVD
variable {m n k p : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
  {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}

/-- Transpose preserves the truncation matched to a supplied SVD witness.
Horn–Johnson 2013, Section 2.6; unlike independently chosen truncations, the
witnesses are paired also at singular-value ties. -/
theorem truncatedMatrix_transpose (h : IsSVD A U V) (k : ℕ) :
    h.transpose.truncatedMatrix k = (h.truncatedMatrix k)ᵀ := by
  simp only [truncatedMatrix, singularValues_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, transpose_rectDiag, Matrix.mul_assoc]

/-- The matched SVD tail annihilates the selected right singular frame.
Wedin (1972), Section 3. -/
theorem sub_truncatedMatrix_mul_headColumns_eq_zero (h : IsSVD A U V) (hkn : k ≤ n) :
    (A - h.truncatedMatrix k) * headColumns V hkn = 0 := by
  have hV : HasOrthonormalCols (headColumns V hkn) :=
    hasOrthonormalCols_headColumns h.transpose_mul_right hkn
  rw [← h.mul_headColumns_projector hkn, Matrix.sub_mul,
    Matrix.mul_assoc A (headColumns V hkn * (headColumns V hkn)ᵀ),
    Matrix.mul_assoc (headColumns V hkn), hV, Matrix.mul_one, sub_self]

/-- Tail multiplication on the complementary right coordinates is exactly the
left projected original multiplication. Wedin (1972), Section 3; the ambient
form includes every unmatched rectangular null direction. -/
theorem sub_truncatedMatrix_mul_residual_headColumns (h : IsSVD A U V)
    (hkm : k ≤ m) (hkn : k ≤ n) (Z : Matrix (Fin n) (Fin p) ℝ) :
    (A - h.truncatedMatrix k) * residual (headColumns V hkn) Z =
      residual (headColumns U hkm) (A * Z) := by
  rw [residual, Matrix.mul_sub, ← Matrix.mul_assoc (A - h.truncatedMatrix k),
    h.sub_truncatedMatrix_mul_headColumns_eq_zero hkn, Matrix.zero_mul, sub_zero,
    ← h.residual_headColumns_eq_sub_truncatedMatrix hkm, residual_mul]

/-- The transpose tail satisfies the paired complementary-coordinate identity.
Wedin (1972), Section 3; no square-shape or nonempty-complement premise occurs. -/
theorem sub_truncatedMatrix_transpose_mul_residual_headColumns (h : IsSVD A U V)
    (hkm : k ≤ m) (hkn : k ≤ n) (Z : Matrix (Fin m) (Fin p) ℝ) :
    (A - h.truncatedMatrix k)ᵀ * residual (headColumns U hkm) Z =
      residual (headColumns V hkn) (Aᵀ * Z) := by
  have hh := h.transpose.sub_truncatedMatrix_mul_residual_headColumns hkn hkm Z
  rw [h.truncatedMatrix_transpose k] at hh
  simpa only [Matrix.transpose_sub] using hh

end IsSVD
end NLAlib

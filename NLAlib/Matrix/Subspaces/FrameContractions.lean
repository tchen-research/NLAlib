import NLAlib.Matrix.Subspaces.Projections
/-!
# Contractions by orthonormal frames

Spectral and Frobenius compression inequalities used in subspace and
pseudoinverse perturbation. Source: Stewart–Sun §I.5 and §V.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- Left compression by an orthonormal frame is a spectral contraction.
Stewart–Sun §I.5. -/
theorem specNorm_transpose_frame_mul_le {Q : Matrix m r ℝ}
    (hQ : HasOrthonormalCols Q) (E : Matrix m n ℝ) : specNorm (Qᵀ*E) ≤ specNorm E := by
  calc
    _ ≤ specNorm Qᵀ*specNorm E := specNorm_mul_le _ _
    _ ≤ 1*specNorm E := mul_le_mul_of_nonneg_right
      (by rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hQ) (specNorm_nonneg _)
    _ = _ := one_mul _

/-- Right compression by an orthonormal frame is a spectral contraction.
Stewart–Sun §I.5. -/
theorem specNorm_mul_frame_le {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (E : Matrix m n ℝ) : specNorm (E*Q) ≤ specNorm E := by
  calc
    _ ≤ specNorm E*specNorm Q := specNorm_mul_le _ _
    _ ≤ specNorm E*1 := mul_le_mul_of_nonneg_left
      (specNorm_le_one_of_orthonormal hQ) (specNorm_nonneg _)
    _ = _ := mul_one _

omit [DecidableEq m] [DecidableEq n] in
/-- Left orthonormal compression is also a Frobenius contraction.
Stewart–Sun §I.5. -/
theorem frobNorm_transpose_frame_mul_le {Q : Matrix m r ℝ}
    (hQ : HasOrthonormalCols Q) (E : Matrix m n ℝ) : frobNorm (Qᵀ*E) ≤ frobNorm E := by
  have hh := frobSq_transpose_mul_le hQ E
  exact Real.sqrt_le_sqrt hh

omit [DecidableEq m] [DecidableEq n] in
/-- Right orthonormal compression is a Frobenius contraction.
Stewart–Sun §I.5. -/
theorem frobNorm_mul_frame_le {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (E : Matrix m n ℝ) : frobNorm (E*Q) ≤ frobNorm E := by
  have hh := frobNorm_transpose_frame_mul_le hQ Eᵀ
  rw [← Matrix.transpose_mul, frobNorm_transpose, frobNorm_transpose] at hh
  exact hh

omit [DecidableEq m] in
/-- The Frobenius norm of a frame is the square root of its column count.
Stewart–Sun §I.5. -/
theorem frobNorm_frame_eq_sqrt_card {Q : Matrix m r ℝ} (hQ : HasOrthonormalCols Q) :
    frobNorm Q = Real.sqrt (Fintype.card r) := by
  rw [frobNorm, frobSq, frobInner_eq_trace, hQ.transpose_mul_self, Matrix.trace_one]

/-- Multiplication by a width-`k` orthonormal frame has Frobenius norm at
most `sqrt(k)` times the original spectral norm. Stewart–Sun §V.3. -/
theorem frobNorm_mul_frame_le_sqrt_card_mul_specNorm {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (E : Matrix m n ℝ) :
    frobNorm (E*Q) ≤ Real.sqrt (Fintype.card r)*specNorm E := by
  have hh := frobNorm_mul_le_specNorm_mul_frobNorm E Q
  rw [frobNorm_frame_eq_sqrt_card hQ, mul_comm] at hh
  exact hh

end NLAlib

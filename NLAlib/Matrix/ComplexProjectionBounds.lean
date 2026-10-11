import NLAlib.Matrix.ComplexVolumeProjection
import NLAlib.Matrix.ComplexVolumeProjectorTrace

/-!
# Complex projection and orthogonal-block norm bounds

These bounds use Mathlib's operator and Frobenius norms on actual complex
matrices and the genuine Hilbert column projector. They include empty index
types, so no artificial positive-dimensional assumption is needed.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n k r : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- A complex Hermitian idempotent has operator norm at most one, including the
empty projector. Source: manuscript `sa:filter`, orthogonal projection contraction. -/
theorem norm_le_one_of_isHermitian_of_isIdempotentElem {P : Matrix m m ℂ}
    (hP : P.IsHermitian) (hPP : IsIdempotentElem P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.eq, show P * P = P from hPP] at h
  nlinarith [norm_nonneg P]

/-- The complementary actual column projector is a contractive complex projection.
Source: manuscript `sa:filter`, its one-competitor argument. -/
theorem norm_one_sub_complexColumnProjector_le (B : Matrix m k ℂ) :
    ‖(1 : Matrix m m ℂ) - complexColumnProjector B‖ ≤ 1 := by
  apply norm_le_one_of_isHermitian_of_isIdempotentElem
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (complexColumnProjector_isHermitian B).eq]
  · change (1 - complexColumnProjector B) * (1 - complexColumnProjector B) = _
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, complexColumnProjector_mul_self]
    abel

/-- The actual complex column-projection residual contracts the operator norm.
Source: manuscript `sa:filter`, orthogonal projection contraction. -/
theorem norm_sub_complexColumnProjector_mul_le (B : Matrix m k ℂ) (A : Matrix m n ℂ) :
    ‖A - complexColumnProjector B * A‖ ≤ ‖A‖ := by
  rw [show A - complexColumnProjector B * A = (1 - complexColumnProjector B) * A by
    rw [Matrix.sub_mul, Matrix.one_mul]]
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_one_sub_complexColumnProjector_le B) (norm_nonneg A)).trans_eq
      (one_mul _))

omit [DecidableEq m] in
/-- Complex orthonormal columns preserve the operator norm on the left.
Source: manuscript `sa:filter`, unitary invariance of the competitor norm. -/
theorem norm_mul_left_of_conjTranspose_mul_eq_one {U : Matrix m k ℂ}
    (hU : Uᴴ * U = 1) (B : Matrix k n ℂ) : ‖U * B‖ = ‖B‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (U * B)
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU,
    Matrix.one_mul, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (U * B), norm_nonneg B]

/-- Complex orthonormal columns preserve the operator norm on the right through
their adjoint. Source: manuscript `sa:filter`, unitary invariance. -/
theorem norm_mul_conjTranspose_right_of_conjTranspose_mul_eq_one {U : Matrix n k ℂ}
    (hU : Uᴴ * U = 1) (B : Matrix m k ℂ) : ‖B * Uᴴ‖ = ‖B‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (B * Uᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    norm_mul_left_of_conjTranspose_mul_eq_one hU, Matrix.l2_opNorm_conjTranspose]

/-- Row-orthogonal complex summands obey the exact squared operator bound.
Source: manuscript `sa:filter`, the row-Gram Pythagorean competitor argument. -/
theorem norm_add_sq_le_of_mul_conjTranspose_eq_zero {X Y : Matrix m n ℂ}
    (h : X * Yᴴ = 0) : ‖X + Y‖ ^ 2 ≤ ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have h' : Y * Xᴴ = 0 := by
    have ht := congrArg Matrix.conjTranspose h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using ht
  have hG : (X + Y) * (X + Y)ᴴ = X * Xᴴ + Y * Yᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h']
    abel
  have hRow : ∀ Z : Matrix m n ℂ, ‖Z * Zᴴ‖ = ‖Z‖ ^ 2 := by
    intro Z
    have ht := Matrix.l2_opNorm_conjTranspose_mul_self Zᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at ht
    simpa only [pow_two] using ht
  rw [← hRow, hG]
  exact (norm_add_le _ _).trans_eq (by rw [hRow, hRow])

section Frobenius
open scoped Matrix.Norms.Frobenius

omit [DecidableEq m] [DecidableEq n] in
/-- The complex squared Frobenius norm also equals the real row-Gram trace.
Source: manuscript `sa:filter`, trace representation of Frobenius mass. -/
theorem frobenius_norm_sq_eq_re_trace_mul_conjTranspose (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = (A * Aᴴ).trace.re := by
  rw [← Matrix.frobenius_norm_conjTranspose A,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [DecidableEq m] [DecidableEq n] in
/-- Complex orthonormal columns preserve squared Frobenius mass on the left.
Source: manuscript `sa:filter`, unitary invariance. -/
theorem frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one {U : Matrix m k ℂ}
    (hU : Uᴴ * U = 1) (B : Matrix k n ℂ) : ‖U * B‖ ^ 2 = ‖B‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- Complex orthonormal columns preserve squared Frobenius mass on the right
through their adjoint. Source: manuscript `sa:filter`, unitary invariance. -/
theorem frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one
    {U : Matrix n k ℂ} (hU : Uᴴ * U = 1) (B : Matrix m k ℂ) :
    ‖B * Uᴴ‖ ^ 2 = ‖B‖ ^ 2 := by
  rw [← Matrix.frobenius_norm_conjTranspose (B * Uᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one hU,
    Matrix.frobenius_norm_conjTranspose]

omit [DecidableEq m] [DecidableEq n] in
/-- Row-orthogonal complex summands have exactly additive squared Frobenius mass.
Source: manuscript `sa:filter`, orthogonal-block competitor. -/
theorem frobenius_norm_add_sq_eq_of_mul_conjTranspose_eq_zero {X Y : Matrix m n ℂ}
    (h : X * Yᴴ = 0) : ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have h' : Y * Xᴴ = 0 := by
    have ht := congrArg Matrix.conjTranspose h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using ht
  rw [frobenius_norm_sq_eq_re_trace_mul_conjTranspose,
    frobenius_norm_sq_eq_re_trace_mul_conjTranspose,
    frobenius_norm_sq_eq_re_trace_mul_conjTranspose,
    Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h',
    add_zero, zero_add, Matrix.trace_add, Complex.add_re]

omit [DecidableEq n] in
/-- Complementary projection splits squared Frobenius mass on the left.
Source: manuscript `sa:filter`, orthogonal projection Pythagoras. -/
theorem frobenius_norm_sq_eq_left_projection_add_residual
    (P : Matrix m m ℂ) (hP : P.IsHermitian) (hPP : IsIdempotentElem P)
    (A : Matrix m n ℂ) : ‖A‖ ^ 2 = ‖P * A‖ ^ 2 + ‖(1 - P) * A‖ ^ 2 := by
  have h := frobenius_norm_sq_eq_right_projection_add_residual P hP hPP Aᴴ
  rw [Matrix.frobenius_norm_conjTranspose] at h
  have h1 : ‖Aᴴ * P‖ = ‖P * A‖ := by
    rw [← Matrix.frobenius_norm_conjTranspose (Aᴴ * P), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.eq]
  have h2 : ‖Aᴴ * (1 - P)‖ = ‖(1 - P) * A‖ := by
    rw [← Matrix.frobenius_norm_conjTranspose (Aᴴ * (1 - P)), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hP.eq]
  rwa [h1, h2] at h

omit [DecidableEq n] in
/-- The genuine complex column residual contracts squared Frobenius mass.
Source: manuscript `sa:filter`, projection competitor. -/
theorem frobenius_norm_sub_complexColumnProjector_mul_sq_le
    (B : Matrix m k ℂ) (A : Matrix m n ℂ) :
    ‖A - complexColumnProjector B * A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have hs := frobenius_norm_sq_eq_left_projection_add_residual (complexColumnProjector B)
    (complexColumnProjector_isHermitian B) (complexColumnProjector_mul_self B) A
  rw [Matrix.sub_mul, Matrix.one_mul] at hs
  linarith [sq_nonneg ‖complexColumnProjector B * A‖]

end Frobenius
end NLAlib

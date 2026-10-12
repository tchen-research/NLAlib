import NLAlib.Matrix.Perturbation.PseudoinverseProjectors
/-!
# The Moore–Penrose difference identity

The exact three-term identity holds at every rank, including rectangular
and empty matrices. Its orthogonal block form supports the sharp perturbation
constants. Source: Stewart–Sun §III.3; atlas `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- A Moore–Penrose inverse is fixed by its own column-range projector,
expressed using transposes. Stewart–Sun §III.3, Penrose identities. -/
theorem moorePenroseInverse_mul_transpose_mul_transpose (A : Matrix m n ℝ) :
    moorePenroseInverse A*(moorePenroseInverse A)ᵀ*Aᵀ = moorePenroseInverse A := by
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul,
    (isMoorePenroseInverse A).transpose_mul_eq, ← Matrix.mul_assoc,
    moorePenroseInverse_mul_moorePenroseInverse]

omit [DecidableEq n] in
/-- The complementary column-space projector annihilates the original
matrix. Stewart–Sun §III.3, including rank zero. -/
theorem complement_columnProjector_mul_eq_zero (A : Matrix m n ℝ) :
    (1-A*moorePenroseInverse A)*A = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, mul_moorePenroseInverse_mul, sub_self]

omit [DecidableEq m] in
/-- The complementary row-space projector is annihilated on the left
by the original matrix. Stewart–Sun §III.3. -/
theorem mul_complement_rowProjector_eq_zero (A : Matrix m n ℝ) :
    A*(1-moorePenroseInverse A*A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    mul_moorePenroseInverse_mul, sub_self]

omit [DecidableEq n] in
/-- An adjoint matrix annihilates the complementary column projector.
Stewart–Sun §III.3, by the projector symmetry and transpose. -/
theorem transpose_mul_complement_columnProjector_eq_zero (A : Matrix m n ℝ) :
    Aᵀ*(1-A*moorePenroseInverse A) = 0 := by
  have hh := congrArg Matrix.transpose (complement_columnProjector_mul_eq_zero A)
  simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    (isMoorePenroseInverse A).transpose_mul_eq, Matrix.transpose_zero] using hh

omit [DecidableEq m] in
/-- The complementary row projector annihilates the adjoint matrix.
Stewart–Sun §III.3, by the projector symmetry and transpose. -/
theorem complement_rowProjector_mul_transpose_eq_zero (A : Matrix m n ℝ) :
    (1-moorePenroseInverse A*A)*Aᵀ = 0 := by
  have hh := congrArg Matrix.transpose (mul_complement_rowProjector_eq_zero A)
  simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    (isMoorePenroseInverse A).transpose_inv_mul_eq, Matrix.transpose_zero] using hh

/-- The exact Moore–Penrose difference identity with its three signs and
complementary range projectors (Wedin's identity):
`B⁺ - A⁺ = -B⁺ (B - A) A⁺ + B⁺ B⁺ᵀ (B - A)ᵀ (I - A A⁺) + (I - B⁺ B) (B - A)ᵀ A⁺ᵀ A⁺`.
Wedin 1973, Thm 4.1 (proof); Stewart–Sun 1990, §III.3; no rank condition is needed.
atlas: pseudoinverse-perturbation (partial) -/
theorem moorePenroseInverse_sub_eq (A B : Matrix m n ℝ) :
    moorePenroseInverse B-moorePenroseInverse A =
      -moorePenroseInverse B*(B-A)*moorePenroseInverse A +
      moorePenroseInverse B*(moorePenroseInverse B)ᵀ*(B-A)ᵀ*
        (1-A*moorePenroseInverse A) +
      (1-moorePenroseInverse B*B)*(B-A)ᵀ*(moorePenroseInverse A)ᵀ*
        moorePenroseInverse A := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  have hb : b*bᵀ*Bᵀ = b := moorePenroseInverse_mul_transpose_mul_transpose B
  have ha : Aᵀ*aᵀ*a = a := by
    rw [← Matrix.transpose_mul, (isMoorePenroseInverse A).transpose_inv_mul_eq]
    exact moorePenroseInverse_mul_moorePenroseInverse A
  have ha0 : Aᵀ*(1-A*a)=0 := transpose_mul_complement_columnProjector_eq_zero A
  have hb0 : (1-b*B)*Bᵀ=0 := complement_rowProjector_mul_transpose_eq_zero B
  change b-a = -b*(B-A)*a + b*bᵀ*(B-A)ᵀ*(1-A*a) + (1-b*B)*(B-A)ᵀ*aᵀ*a
  rw [Matrix.transpose_sub, Matrix.mul_sub (b*bᵀ), Matrix.sub_mul,
    hb, Matrix.mul_assoc (b*bᵀ) Aᵀ, ha0, Matrix.mul_zero, sub_zero,
    Matrix.mul_sub (1-b*B), hb0, zero_sub]
  simp only [Matrix.neg_mul]
  rw [show (1-b*B)*Aᵀ*aᵀ*a = (1-b*B)*(Aᵀ*aᵀ*a) by simp only [Matrix.mul_assoc], ha]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

end NLAlib

import NLAlib.Matrix.Perturbation.PseudoinverseDifference
/-!
# The orthogonal blocks of a Moore–Penrose difference

These exact identities expose the three nonzero orthogonal blocks and their
complementary-domain factors. Stewart–Sun §III.3;
atlas `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The four orthogonal blocks of the pseudoinverse difference, with the
lower-right block zero. Stewart–Sun §III.3, from the Penrose identities. -/
theorem moorePenroseInverse_sub_blocks (A B : Matrix m n ℝ) :
    let a := moorePenroseInverse A
    let b := moorePenroseInverse B
    let P := A*a
    let Q := b*B
    Q*(b-a)*P = -b*(B-A)*a ∧
    Q*(b-a)*(1-P) = b*(1-P) ∧
    (1-Q)*(b-a)*P = -(1-Q)*a ∧
    (1-Q)*(b-a)*(1-P) = 0 := by
  dsimp only
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  have ha : a*A*a=a := moorePenroseInverse_mul_moorePenroseInverse A
  have hb : b*B*b=b := moorePenroseInverse_mul_moorePenroseInverse B
  have hcA : a*(1-A*a)=0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ha, sub_self]
  have hcB : (1-b*B)*b=0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hb, sub_self]
  change (b*B)*(b-a)*(A*a) = -b*(B-A)*a ∧
    (b*B)*(b-a)*(1-A*a) = b*(1-A*a) ∧
    (1-b*B)*(b-a)*(A*a) = -(1-b*B)*a ∧
    (1-b*B)*(b-a)*(1-A*a)=0
  constructor
  · rw [Matrix.mul_sub, Matrix.sub_mul, hb]
    have haa : a*(A*a)=a := by rw [← Matrix.mul_assoc, ha]
    rw [Matrix.mul_assoc (b*B) a, haa]
    conv_rhs => rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, neg_sub]
    simp only [Matrix.mul_assoc]
  constructor
  · rw [Matrix.mul_sub (b*B) b a, Matrix.sub_mul, hb, Matrix.mul_assoc (b*B) a, hcA,
      Matrix.mul_zero, sub_zero]
  constructor
  · rw [Matrix.mul_sub (1-b*B) b a, Matrix.sub_mul, hcB, Matrix.zero_mul, zero_sub,
      Matrix.mul_assoc (1-b*B) a, ← Matrix.mul_assoc a A, ha]
    rw [Matrix.neg_mul]
  · rw [Matrix.mul_sub (1-b*B) b a, Matrix.sub_mul, hcB, Matrix.zero_mul,
      Matrix.mul_assoc (1-b*B) a, hcA, Matrix.mul_zero, sub_self]

omit [DecidableEq n] in
/-- The upper-right pseudoinverse block has a perturbation-adjoint
factor and a complementary column-space factor. Stewart–Sun §III.3. -/
theorem moorePenroseInverse_mul_complement_columnProjector_eq (A B : Matrix m n ℝ) :
    moorePenroseInverse B*(1-A*moorePenroseInverse A) =
      moorePenroseInverse B*(moorePenroseInverse B)ᵀ*(B-A)ᵀ*(1-A*moorePenroseInverse A) := by
  rw [Matrix.transpose_sub, Matrix.mul_sub (moorePenroseInverse B*(moorePenroseInverse B)ᵀ) Bᵀ Aᵀ, Matrix.sub_mul,
    moorePenroseInverse_mul_transpose_mul_transpose B,
    Matrix.mul_assoc _ Aᵀ, transpose_mul_complement_columnProjector_eq_zero A,
    Matrix.mul_zero, sub_zero]

omit [DecidableEq m] in
/-- The lower-left pseudoinverse block has the complementary row-space
factor and a perturbation-adjoint factor. Stewart–Sun §III.3. -/
theorem neg_complement_rowProjector_mul_moorePenroseInverse_eq (A B : Matrix m n ℝ) :
    -(1-moorePenroseInverse B*B)*moorePenroseInverse A =
      (1-moorePenroseInverse B*B)*(B-A)ᵀ*(moorePenroseInverse A)ᵀ*moorePenroseInverse A := by
  let a := moorePenroseInverse A
  have ha : Aᵀ*aᵀ*a=a := by
    rw [← Matrix.transpose_mul, (isMoorePenroseInverse A).transpose_inv_mul_eq]
    exact moorePenroseInverse_mul_moorePenroseInverse A
  rw [Matrix.transpose_sub, Matrix.mul_sub,
    complement_rowProjector_mul_transpose_eq_zero B, zero_sub]
  simp only [Matrix.neg_mul]
  rw [show (1-moorePenroseInverse B*B)*Aᵀ*aᵀ*a =
    (1-moorePenroseInverse B*B)*(Aᵀ*aᵀ*a) by simp only [Matrix.mul_assoc], ha]

omit [DecidableEq n] in
/-- The one-sided column-space gap contains the perturbation and the first
pseudoinverse as actual factors. Stewart–Sun §III.3, all ranks. -/
theorem complement_columnProjector_mul_columnProjector_eq (A B : Matrix m n ℝ) :
    (1-B*moorePenroseInverse B)*(A*moorePenroseInverse A) =
      -((1-B*moorePenroseInverse B)*(B-A)*moorePenroseInverse A) := by
  rw [Matrix.mul_sub, complement_columnProjector_mul_eq_zero B, zero_sub]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  simp

omit [DecidableEq m] in
/-- The one-sided row-space gap contains the second pseudoinverse and the
perturbation as actual factors. Stewart–Sun §III.3, all ranks. -/
theorem rowProjector_mul_complement_rowProjector_eq (A B : Matrix m n ℝ) :
    (moorePenroseInverse B*B)*(1-moorePenroseInverse A*A) =
      moorePenroseInverse B*(B-A)*(1-moorePenroseInverse A*A) := by
  rw [Matrix.mul_sub (moorePenroseInverse B) B A, Matrix.sub_mul,
    Matrix.mul_assoc (moorePenroseInverse B) A,
    mul_complement_rowProjector_eq_zero A, Matrix.mul_zero, sub_zero]

end NLAlib

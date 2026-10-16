import NLAlib.Matrix.Norms.Core

/-! # Frobenius invariance under orthonormal frames and unitary factors -/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {K m n p : Type*} [RCLike K] [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

/-- Left multiplication by an orthonormal frame preserves the Frobenius norm. -/
theorem frobNorm_mul_left_of_hasOrthonormalCols (U : Matrix m n K) (X : Matrix n p K)
    (hU : HasOrthonormalCols U) : frobNorm (U * X) = frobNorm X := by
  have hs : frobNorm (U * X) ^ 2 = frobNorm X ^ 2 := by
    rw [frobNorm_sq, frobNorm_sq, frobSq_eq_re_trace_conjTranspose_mul_self,
      frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U X, hU, Matrix.one_mul]
  nlinarith [frobNorm_nonneg (U * X), frobNorm_nonneg X]

/-- Right multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_mul_right_unitary (X : Matrix m n K) (U : Matrix.unitaryGroup n K) :
    frobNorm (X * (U : Matrix n n K)) = frobNorm X := by
  rw [← frobNorm_conjTranspose (X * (U : Matrix n n K)), Matrix.conjTranspose_mul,
    frobNorm_mul_left_of_hasOrthonormalCols _ Xᴴ, frobNorm_conjTranspose]
  change ((U : Matrix n n K)ᴴ)ᴴ * (U : Matrix n n K)ᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact Unitary.coe_mul_star_self U

/-- Left multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_mul_left_unitary (U : Matrix.unitaryGroup n K) (X : Matrix n p K) :
    frobNorm ((U : Matrix n n K) * X) = frobNorm X :=
  frobNorm_mul_left_of_hasOrthonormalCols _ _ (Unitary.coe_star_mul_self U)

end NLAlib

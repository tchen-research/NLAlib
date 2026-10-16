import NLAlib.Matrix.Norms.Core
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Frobenius norms of the two Gram matrices -/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n]

/-- The row and column Gram matrices have equal Frobenius norm, including
rectangular and empty matrices. The identity permits a residual Gram norm
to be evaluated in the smaller column space. Source: the trace cycle identity. -/
theorem frobNorm_mul_conjTranspose_eq_conjTranspose_mul (W : Matrix m n K) :
    frobNorm (W * Wᴴ) = frobNorm (Wᴴ * W) := by
  have ht : Matrix.trace ((W * Wᴴ)ᴴ * (W * Wᴴ)) =
      Matrix.trace ((Wᴴ * W)ᴴ * (Wᴴ * W)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Matrix.trace (W * (Wᴴ * W * Wᴴ)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Wᴴ * W * Wᴴ) * W) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hs : frobNorm (W * Wᴴ) ^ 2 = frobNorm (Wᴴ * W) ^ 2 := by
    rw [frobNorm_sq, frobNorm_sq, frobSq_eq_re_trace_conjTranspose_mul_self,
      frobSq_eq_re_trace_conjTranspose_mul_self, ht]
  nlinarith [frobNorm_nonneg (W * Wᴴ), frobNorm_nonneg (Wᴴ * W)]

end NLAlib

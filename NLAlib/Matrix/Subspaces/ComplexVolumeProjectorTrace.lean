import NLAlib.Matrix.Norms.ComplexFrobeniusTrace
import NLAlib.Matrix.Subspaces.ProjectorTrace

/-!
# Complex orthogonal projector trace and diagonal budgets

Squared Frobenius mass splits over complementary complex orthogonal projectors.
The field-generic trace-equals-rank identity and the diagonal capture budgets are
`trace_eq_rank_of_isIdempotentElem` and `re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem`
(`NLAlib.Matrix.Subspaces.ProjectorTrace`). Source: Frobenius Eckart–Young proof;
supports `sa:volume-theorem` and `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

/-- Real squared Frobenius mass splits over complementary complex
orthogonal projectors on the right. Source: `sa:volume-theorem`. -/
theorem frobenius_norm_sq_eq_right_projection_add_residual
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ‖A * P‖ ^ 2 + ‖A * (1 - P)‖ ^ 2 := by
  have hleft : (A * P)ᴴ * (A * P) = P * (Aᴴ * A) * P := by
    simp only [Matrix.conjTranspose_mul, hs.eq, Matrix.mul_assoc]
  have hright : (A * (1 - P))ᴴ * (A * (1 - P)) =
      (1 - P) * (Aᴴ * A) * (1 - P) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hs.eq, Matrix.mul_assoc]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one, show P * P = P from hp]
    abel
  have htleft : (P * (Aᴴ * A) * P).trace = (P * (Aᴴ * A)).trace := by
    rw [Matrix.trace_mul_cycle, show P * P = P from hp]
  have htright : ((1 - P) * (Aᴴ * A) * (1 - P)).trace =
      ((1 - P) * (Aᴴ * A)).trace := by
    rw [Matrix.trace_mul_cycle, hcomp]
  rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul, hleft, hright, htleft, htright]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  ring

end NLAlib

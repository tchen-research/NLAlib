import NLAlib.Matrix.ComplexFrobenius
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Complex Frobenius trace and column identities

These standard identities bridge the actual Hilbert-space projection
residuals to Mathlib's Frobenius norm. Source: `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

/-- The squared complex Frobenius norm equals the real Gram trace.
Source: the entrywise Frobenius identity; supports `volume-sampling`. -/
theorem frobenius_norm_sq_eq_re_trace_conjTranspose_mul
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = (Aᴴ * A).trace.re := by
  rw [frobenius_norm_sq_eq_sum_norm_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Squared Frobenius error is the sum of the squared errors in actual
complex columns. Source: `sa:volume-theorem`, finite column summation. -/
theorem frobenius_norm_sq_eq_sum_single_columns
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ j, ‖A.submatrix id (fun _ : Fin 1 => j)‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum_norm_sq, Matrix.submatrix_apply,
    id_eq, Fin.sum_univ_one]
  rw [Finset.sum_comm]

end NLAlib

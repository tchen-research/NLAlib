import NLAlib.Matrix.Norms

/-! # Squared Frobenius norms as sums of column errors -/
noncomputable section
namespace NLAlib

/-- The squared Frobenius norm is the sum of the squared norms of its individual
columns, represented as one-column matrices. Source: HMT (2011), §2.1;
manuscript `sa:volume-theorem`, projection-error sum. -/
theorem frobSq_eq_sum_frobSq_single_columns {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    frobSq A = ∑ j, frobSq (A.submatrix id (fun _ : Fin 1 => j)) := by
  simp only [frobSq, frobInner, Matrix.submatrix_apply, id_eq, Fin.sum_univ_one]
  rw [Finset.sum_comm]

end NLAlib

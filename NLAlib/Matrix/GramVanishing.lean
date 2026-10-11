import NLAlib.Matrix.Norms
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Vanishing rows of positive semidefinite matrices

A zero diagonal entry forces its entire Gram column and row to vanish. This
handles zero-probability pivots in finite Cholesky transition sums.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib

/-- A zero diagonal of a real positive semidefinite matrix forces its corresponding
column to vanish. Source: manuscript `sa:rp-one-step`, zero-probability pivot case;
standard Gram-factor Cauchy--Schwarz. -/
theorem apply_eq_zero_of_posSemidef_of_diag_eq_zero {n : Type*}
    [Fintype n] [DecidableEq n] {R : Matrix n n ℝ} (hR : R.PosSemidef)
    {i : n} (hi : R i i = 0) (j : n) : R j i = 0 := by
  obtain ⟨F, hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hGram : R = Fᵀ * F := by
    rw [hF, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsum : ∑ a, (F a i) ^ 2 = 0 := by
    have h := hi
    rw [hGram] at h
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hzero : ∀ a, F a i = 0 := by
    intro a
    apply eq_zero_of_pow_eq_zero (n := 2)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (F b i)).mp hsum a
      (Finset.mem_univ a)
  rw [hGram]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hzero, mul_zero, Finset.sum_const_zero]

/-- A real finite matrix of rank zero is zero. Source: rank--range identity;
manuscript `sa:rp-rank`, zero-rank termination. -/
theorem eq_zero_of_matrix_rank_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    {R : Matrix m n ℝ} (hR : R.rank = 0) : R = 0 := by
  have hrange : LinearMap.range R.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hR
  ext i j
  have hj : R.col j ∈ LinearMap.range R.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  rw [hrange, Submodule.mem_bot] at hj
  exact congrFun hj i

end NLAlib

import NLAlib.Solvers.LeastSquares.FrameDecomposition
import NLAlib.Matrix.Basic.GramVanishing

/-! # Exact full-width and rank-zero sketch-and-solve boundaries -/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {K : Type*} [RCLike K] {n d p ell : ℕ}

/-- Any square orthonormal sketch recovers the exact original minimum-norm
least-squares solution, for both fields and arbitrary input rank.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem sketchAndSolve_eq_of_square_orthonormal_sketch
    (A : Matrix (Fin n) (Fin d) K) (B : Matrix (Fin n) (Fin p) K)
    (Ω : Matrix (Fin n) (Fin n) K) (hΩ : HasOrthonormalCols Ω) :
    sketchAndSolve A Ωᴴ B=moorePenroseInverse A*B := by
  have hright : Ω*Ωᴴ=1 := mul_eq_one_comm.mp hΩ.conjTranspose_mul_self
  have ht : HasOrthonormalCols Ωᴴ := by
    rw [HasOrthonormalCols,Matrix.conjTranspose_conjTranspose]
    exact hright
  unfold sketchAndSolve
  rw [moorePenroseInverse_mul_left_of_hasOrthonormalCols Ωᴴ A ht,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ω Ωᴴ B,hright,Matrix.one_mul]

/-- Rank zero gives exactly zero solution and the original right-hand-side
residual for every sketch, with no probability or width restrictions.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem sketchAndSolve_eq_zero_and_residual_of_rank_eq_zero
    (A : Matrix (Fin n) (Fin d) K) (S : Matrix (Fin ell) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) (hA : A.rank=0) :
    sketchAndSolve A S B=0 ∧ frobSq (B-A*sketchAndSolve A S B)=frobSq B := by
  have hz : A=0 := eq_zero_of_matrix_rank_eq_zero hA
  subst A
  simp [sketchAndSolve_zero]

end NLAlib

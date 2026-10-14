import NLAlib.Krylov.Quadrature.JacobiFraction
import NLAlib.Matrix.Structured.TridiagonalSpectrum

/-! # Simple Jacobi spectra and positive Gauss weights

The nonzero off-diagonals of every valid Lanczos decomposition make its Jacobi
spectrum simple and every squared first eigenvector coordinate positive.
Source: Gautschi (2004), Theorems 1.19 and 1.46.
Atlas: `orthogonal-polynomial-zeros`.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

private theorem isUpperHessenberg_transpose_T (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) : IsUpperHessenberg D.Tᵀ := by
  intro i j hij
  apply D.T_apply_eq_zero_of_one_lt_dist hA
  simp only [lt_abs]
  right
  omega

private theorem T_superdiagonal_ne_zero (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    (i j : Fin q) (hij : i.val + 1 = j.val) : D.T i j ≠ 0 := by
  have hb := D.beta_ne_zero (j := j.val) (by omega) j.isLt
  rw [beta, dif_pos ⟨by omega, j.isLt⟩] at hb
  rw [← (D.isSymm_T hA).apply]
  convert hb using 2
  exact Fin.ext (by simp; omega)

/-- Every Gauss eigenvector has a nonzero first coordinate, including a terminal
Lanczos decomposition. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial), jacobi-matrix-identities (partial) -/
theorem eigenvectorBasis_T_apply_zero_ne_zero (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (i : Fin q) :
    (D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩ ≠ 0 :=
  (D.isHermitian_T hA).eigenvectorBasis_apply_zero_ne_zero
    (D.isUpperHessenberg_transpose_T hA) (D.T_superdiagonal_ne_zero hA) hq i

/-- Every normalized Gauss weight is strictly positive. Source: Gautschi (2004),
Theorem 1.46.
atlas: orthogonal-polynomial-zeros (partial), jacobi-matrix-identities (partial) -/
theorem sq_eigenvectorBasis_T_apply_zero_pos (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (i : Fin q) :
    0 < ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 :=
  sq_pos_of_ne_zero (D.eigenvectorBasis_T_apply_zero_ne_zero hA hq i)

/-- The eigenvalues of every Lanczos Jacobi matrix are distinct. Source: Gautschi
(2004), Theorem 1.19. No positivity convention on the basis signs is required.
atlas: orthogonal-polynomial-zeros (partial), jacobi-matrix-identities (partial) -/
theorem eigenvalues_T_injective (D : LanczosDecomp A b q) (hA : A.IsHermitian) :
    Function.Injective (D.isHermitian_T hA).eigenvalues :=
  (D.isHermitian_T hA).eigenvalues_injective_of_unreduced
    (D.isUpperHessenberg_transpose_T hA) (D.T_superdiagonal_ne_zero hA)

end LanczosDecomp

end NLAlib

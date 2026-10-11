import NLAlib.Matrix.MoorePenrose

/-!
# Scalar Moore--Penrose inverses

The Moore--Penrose inverse of a one-by-one real matrix is the totalized scalar
reciprocal. This identifies one-column Nyström with a coordinate Cholesky pivot.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A scalar reciprocal satisfies all four Penrose identities, including at zero.
Source: Horn--Johnson, §7.3; manuscript `sa:rp-update`, one-column core. -/
theorem isMoorePenroseInverse_singleton (a : ℝ) :
    IsMoorePenroseInverse (Matrix.diagonal (fun _ : Fin 1 => a)) (Matrix.diagonal (fun _ : Fin 1 => a⁻¹)) := by
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply, Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1), ite_true]
    by_cases ha : a = 0
    · simp [ha]
    · field_simp
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply, Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1), ite_true]
    by_cases ha : a = 0
    · simp [ha]
    · field_simp
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply, Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1), ite_true]
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply, Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1), ite_true]

/-- The general inverse of a scalar matrix equals its scalar reciprocal, at every rank.
Source: Horn--Johnson, §7.3; manuscript `sa:rp-update`, one-column core. -/
theorem moorePenroseInverse_singleton (a : ℝ) :
    moorePenroseInverse (Matrix.diagonal (fun _ : Fin 1 => a)) = Matrix.diagonal (fun _ : Fin 1 => a⁻¹) :=
  (isMoorePenroseInverse _).unique (isMoorePenroseInverse_singleton a)

end NLAlib

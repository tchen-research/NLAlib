import NLAlib.Matrix.OrderedSchur
import NLAlib.Matrix.Projections

/-!
# Orthogonal diagonalization with a prescribed real root list

For a real symmetric matrix, the ordered real Schur form is diagonal.
This realizes any complete characteristic-root ordering, including repeated
roots, and supplies the actual orthogonal change of coordinates needed to
transport converse-interlacing constructions.
-/
noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real symmetric matrix admits orthogonal diagonalization with any
prescribed complete characteristic-root list. Source: the ordered Schur
and real spectral theorems; helper for the prescribed-matrix clauses of
`interlacing-converse`, with arbitrary finite and empty shapes. -/
theorem exists_orthogonal_diagonalization_of_isHermitian_with_charpoly
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (d : n → ℝ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * Matrix.diagonal d * Qᵀ := by
  let e := (Fintype.equivFin n).symm
  obtain ⟨U, T, hsim, htri, hdiag⟩ :=
    exists_unitary_schur_triangularization_with_charpoly A e d hd
  have hUtU : (U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self U
  have hback : (U : Matrix n n ℝ)ᴴ * A * (U : Matrix n n ℝ) = T := by
    rw [hsim]
    calc
      (U : Matrix n n ℝ)ᴴ * ((U : Matrix n n ℝ) * T * (U : Matrix n n ℝ)ᴴ) *
          (U : Matrix n n ℝ) =
        ((U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ)) * T *
          ((U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ)) := by simp only [Matrix.mul_assoc]
      _ = T := by rw [hUtU, Matrix.one_mul, Matrix.mul_one]
  have hT : T.IsHermitian := hback ▸ Matrix.isHermitian_conjTranspose_mul_mul _ hA
  have hTt : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.eq
  have hD : T = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hdiag i
    · rw [Matrix.diagonal_apply_ne _ hij]
      rcases lt_or_gt_of_ne (fun h => hij (e.symm.injective h)) with hlt | hgt
      · rw [← hTt]
        exact htri j i hlt
      · exact htri i j hgt
  refine ⟨U, ?_, ?_⟩
  · simpa only [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial] using hUtU
  · simpa only [hD, Matrix.conjTranspose_eq_transpose_of_trivial] using hsim

end NLAlib

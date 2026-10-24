import NLAlib.Matrix.Basic.Orthonormal
import NLAlib.Matrix.Norms.Frobenius
import Mathlib.LinearAlgebra.Matrix.RowCol

/-! # Replacing a frame column by an orthogonal residual

The exact Gram determinant is the squared norm of the replacement vector.
This elementary identity is the global Cauchy–Binet input for the sharp
projection-volume interpolation risk.
Source: Dereziński–Warmuth 2018, Theorem 8.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d] [DecidableEq d]

omit [Fintype d] in
/-- Replacing a column of an orthonormal frame by an orthogonal vector gives
a diagonal Gram matrix, with the vector's squared length at that column. -/
theorem conjTranspose_mul_updateCol_of_orthonormal
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (e : n → 𝕜)
    (he : Qᴴ *ᵥ e = 0) (i : d) :
    (Q.updateCol i e)ᴴ * Q.updateCol i e =
      Matrix.diagonal (fun j => if j = i then star e ⬝ᵥ e else 1) := by
  have he' : ∀ j, ∑ a, star (Q a j) * e a = 0 := fun j => congrFun he j
  have heStar : ∀ j, ∑ a, star (e a) * Q a j = 0 := by
    intro j
    have h := congrArg star (he' j)
    simpa only [star_sum, star_mul, star_star, star_zero, mul_comm] using h
  ext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply_eq, dotProduct, Pi.star_apply]
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.updateCol_self,
        Matrix.updateCol_ne hb, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
      exact heStar b
  · by_cases hb : b = i
    · subst b
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.updateCol_ne ha,
        Matrix.updateCol_self, Matrix.diagonal_apply_ne _ ha]
      exact he' a
    · have h := congrFun (congrFun hQ a) b
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.updateCol_ne ha,
        Matrix.updateCol_ne hb]
      rw [h]
      by_cases hab : a = b
      · subst b
        simp [ha]
      · simp [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]

/-- The Gram determinant after replacing a frame column by an orthogonal
vector is its actual squared Euclidean length, also over complex scalars. -/
theorem re_det_gram_updateCol_of_orthonormal
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (e : n → 𝕜)
    (he : Qᴴ *ᵥ e = 0) (i : d) :
    RCLike.re ((Q.updateCol i e)ᴴ * Q.updateCol i e).det = ∑ a, ‖e a‖ ^ 2 := by
  rw [conjTranspose_mul_updateCol_of_orthonormal Q hQ e he i, Matrix.det_diagonal,
    Fintype.prod_ite_eq' i]
  simp only [dotProduct, Pi.star_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

end NLAlib

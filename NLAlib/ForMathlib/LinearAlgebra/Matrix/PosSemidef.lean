import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real positive semidefinite matrices are Gram matrices

`exists_eq_transpose_mul_of_posSemidef`: a real PSD matrix is `FᵀF` for a square `F`, the real
form of Mathlib's `CStarAlgebra.nonneg_iff_eq_star_mul_self` on matrices (with the `L²` operator
norm and the Loewner order scoped in). Used by the Nyström bounds and partial Cholesky.
-/

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- A real positive semidefinite matrix is a Gram matrix: `A = FᵀF` for some square `F`.
Mathlib `CStarAlgebra.nonneg_iff_eq_star_mul_self`. Atlas `nystrom-structural`,
`partial-cholesky-nystrom` (helper). -/
theorem exists_eq_transpose_mul_of_posSemidef [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : ∃ F : Matrix n n ℝ, A = Fᵀ * F := by
  obtain ⟨F, hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨F, by rw [hF, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

end NLAlib

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import NLAlib.Matrix.Norms

/-!
# Orthonormal frames, projectors and residuals

* `NLAlib.HasOrthonormalCols Q`: `Qᵀ Q = I`.
* `NLAlib.residual Q A = A − Q (Qᵀ A) = (I − QQᵀ) A`, the part of `A` outside `range Q`.
* `NLAlib.IsBestRankApprox k C Y`: `Y` has rank `≤ k` and minimises the Frobenius distance to
  `C` among rank-`≤ k` matrices. Until Eckart–Young is proved (atlas `eckart-young`) this
  optimality property is how `⟦C⟧ₖ` enters statements.

Atlas: `projection-facts`, `eckart-young`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-- `Q` has orthonormal columns: `Qᵀ Q = I`. -/
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q ℝ) : Prop := Qᵀ * Q = 1

/-- Residual of `A` after projecting onto the column space of `Q`: `(I − QQᵀ) A`. -/
def residual (Q : Matrix m q ℝ) (A : Matrix m n ℝ) : Matrix m n ℝ := A - Q * (Qᵀ * A)

/-- `Y` is a best rank-`k` Frobenius approximation of `C`. -/
def IsBestRankApprox (k : ℕ) (C Y : Matrix m n ℝ) : Prop :=
  Y.rank ≤ k ∧ ∀ Z : Matrix m n ℝ, Z.rank ≤ k → frobSq (C - Y) ≤ frobSq (C - Z)

/-- The residual is orthogonal to `range Q`. -/
theorem transpose_mul_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : Qᵀ * residual Q A = 0 := by
  unfold residual HasOrthonormalCols at *
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]

end NLAlib

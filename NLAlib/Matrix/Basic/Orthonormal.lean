import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!
# Orthonormal columns and the projection residual

The two definitions every layer uses, placed upstream of `Matrix/Norms` so that norm lemmas can
take `HasOrthonormalCols` hypotheses instead of raw `Pᴴ * P = 1` (F4, decision D1).

* `NLAlib.HasOrthonormalCols Q`: `Qᴴ Q = I` (at `𝕜 = ℝ`: `Qᵀ Q = I`, definitionally).
* `NLAlib.projResidual Q A = A − Q (Qᴴ A) = (I − QQᴴ) A`, the part of `A` outside `range Q`
  (an orthogonal projection only when `Q` has orthonormal columns; not the linear-system
  residual `b − Ax`).

Projectors, Pythagoras and completions are in `Matrix/Subspaces/Projections.lean`.
-/

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-- `Q` has orthonormal columns: `Qᴴ Q = I` (at `𝕜 = ℝ` this is `Qᵀ Q = I` by definition).
atlas: orthonormal-columns-def -/
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q 𝕜) : Prop := Qᴴ * Q = 1

/-- The projection residual of `A` with respect to `Q`: `A − Q (Qᴴ A) = (I − QQᴴ) A`. For `Q`
with orthonormal columns this is the component of `A` orthogonal to `range Q`; for other `Q` it
is just this matrix. Not the linear-system residual `b − Ax`.
atlas: residual-def -/
def projResidual (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) : Matrix m n 𝕜 := A - Q * (Qᴴ * A)

omit [Fintype q] in
/-- Eliminator for `HasOrthonormalCols`: `Qᴴ Q = I`. -/
theorem HasOrthonormalCols.conjTranspose_mul_self [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : Qᴴ * Q = 1 := hQ

omit [Fintype q] in
/-- `HasOrthonormalCols Q` unfolded: `Qᴴ Q = I`. -/
theorem hasOrthonormalCols_iff_conjTranspose_mul_self [DecidableEq q] {Q : Matrix m q 𝕜} :
    HasOrthonormalCols Q ↔ Qᴴ * Q = 1 := Iff.rfl


end NLAlib

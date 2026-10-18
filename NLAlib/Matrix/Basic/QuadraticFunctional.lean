import NLAlib.Matrix.Basic.QuadForm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A fixed-vector quadratic form as a matrix linear functional

The map `A ↦ uᴴ A u` is linear in the matrix, even though it is quadratic in
the vector. Its continuous version lets probability laws push forward directly
to the scalar quadratic observable.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- Evaluation of a matrix quadratic form at a fixed vector is linear in the matrix. -/
def quadFormLinearMap (u : n → 𝕜) : Matrix n n 𝕜 →ₗ[𝕜] 𝕜 where
  toFun A := quadForm A u
  map_add' A B := by simp only [quadForm, Matrix.add_mulVec, dotProduct_add]
  map_smul' r A := by
    simp only [quadForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, RingHom.id_apply]

/-- The fixed-vector matrix linear functional evaluates to the genuine quadratic form. -/
@[simp] theorem quadFormLinearMap_apply (u : n → 𝕜) (A : Matrix n n 𝕜) :
    quadFormLinearMap u A = quadForm A u := rfl

open scoped Matrix.Norms.L2Operator in
/-- A fixed-vector matrix quadratic observable is a continuous linear functional. -/
def quadFormContinuousLinearMap [DecidableEq n] (u : n → 𝕜) : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  (quadFormLinearMap u).toContinuousLinearMap

open scoped Matrix.Norms.L2Operator in
/-- The continuous functional is exactly the quadratic observable. -/
@[simp] theorem quadFormContinuousLinearMap_apply [DecidableEq n]
    (u : n → 𝕜) (A : Matrix n n 𝕜) :
    quadFormContinuousLinearMap u A = quadForm A u := rfl

end NLAlib

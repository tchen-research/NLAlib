import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Rank-one covariance congruence and one-sided order

A rank-one covariance is positive semidefinite, transforms by congruence,
and retains a one-sided centered order bound independently of its vector norm.
-/

noncomputable section

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d]

/-- Applying a linear map to a vector transforms its rank-one covariance
by congruence, including rectangular and singular maps. -/
theorem vecMulVec_mulVec_star_mulVec {m : Type*} [Fintype m]
    (S : Matrix m d 𝕜) (x : d → 𝕜) :
    vecMulVec (S *ᵥ x) (star (S *ᵥ x)) = S * vecMulVec x (star x) * Sᴴ := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

variable [DecidableEq d]

/-- A rank-one covariance minus the identity is bounded below by minus the
identity, without any bound on the vector norm. -/
theorem neg_one_le_vecMulVec_sub_one (x : d → 𝕜) :
    -(1 : Matrix d d 𝕜) ≤ vecMulVec x (star x) - 1 := by
  simpa only [zero_sub] using sub_le_sub_right
    (posSemidef_vecMulVec_self_star x).nonneg (1 : Matrix d d 𝕜)

/-- The negative centered rank-one covariance is bounded above by the
identity, without any bound on the vector norm. -/
theorem one_sub_vecMulVec_le_one (x : d → 𝕜) :
    (1 : Matrix d d 𝕜) - vecMulVec x (star x) ≤ 1 :=
  sub_le_self _ (posSemidef_vecMulVec_self_star x).nonneg

end Matrix

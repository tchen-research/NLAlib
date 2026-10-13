import NLAlib.Matrix.Basic.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Rotations in a plane

* `planeRotation u v c s = I + (c − 1)(u uᵀ + v vᵀ) + s (u vᵀ − v uᵀ)`: the rotation by the
  angle `(c, s) = (cos θ, sin θ)` in the plane spanned by the orthonormal pair `u, v`, the
  identity on its orthogonal complement. It sends `u ↦ c u − s v` and `v ↦ s u + c v`
  (`planeRotation_mulVec`), so for the coordinate pair `u = eᵢ`, `v = eⱼ` it is Golub–Van Loan's
  `G(i, j, θ)` (`givens i j c s`, `Matrix/Factorizations/Givens.lean`, is this coordinate case).
* `hasOrthonormalCols_planeRotation`: orthogonal when `c² + s² = 1` and `u, v` are orthonormal.
* `sq_rational_rotation_coefficients`: the rational parametrisation of the unit circle.

Golub–Van Loan 2013, §5.1.8; Horn–Johnson 2013, §2.1 (plane rotations) and the Schur–Horn
argument of Thm 4.3.48.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **plane rotation** by `(c, s)` in the plane of the orthonormal pair `u, v`:
`I + (c − 1)(u uᵀ + v vᵀ) + s (u vᵀ − v uᵀ)`. For `u = eᵢ`, `v = eⱼ` this is Golub–Van Loan's
`G(i, j, θ)` with `c = cos θ`, `s = sin θ`. For a non-orthonormal pair it is just this matrix.
Golub–Van Loan 2013, §5.1.8. -/
def planeRotation (u v : n → ℝ) (c s : ℝ) : Matrix n n ℝ :=
  1 + (c - 1) • (Matrix.vecMulVec u u + Matrix.vecMulVec v v) +
    s • (Matrix.vecMulVec u v - Matrix.vecMulVec v u)

omit [DecidableEq n] in
/-- `‖u‖ = 1` as a dot product, for real vectors (proof helper). -/
theorem dotProduct_self_eq_one_of_norm_toLp_eq_one {u : n → ℝ}
    (hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖ = 1) : u ⬝ᵥ u = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 u : EuclideanSpace ℝ n)
  rw [hu, one_pow] at h
  rw [dotProduct, h]
  exact Finset.sum_congr rfl fun i _ => (sq (u i)).symm

/-- A plane rotation with `c² + s² = 1` in the plane of an orthonormal pair is orthogonal.
Golub–Van Loan 2013, §5.1.8. -/
theorem hasOrthonormalCols_planeRotation (u v : n → ℝ)
    (hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖ = 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ n)‖ = 1) (huv : u ⬝ᵥ v = 0)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    HasOrthonormalCols (planeRotation u v c s) := by
  have hu := dotProduct_self_eq_one_of_norm_toLp_eq_one hu
  have hv := dotProduct_self_eq_one_of_norm_toLp_eq_one hv
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  rw [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial]
  let P := Matrix.vecMulVec u u + Matrix.vecMulVec v v
  let K := Matrix.vecMulVec u v - Matrix.vecMulVec v u
  have hPP : P * P = P := by
    simp only [P, Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero, add_zero, zero_add]
  have hPK : P * K = K := by
    simp only [P, K, Matrix.add_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero]
    abel
  have hKP : K * P = K := by
    simp only [P, K, Matrix.sub_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero]
    abel
  have hKK : K * K = -P := by
    simp only [P, K, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero, sub_zero, zero_sub]
    abel
  have hPt : Pᵀ = P := by simp [P, Matrix.transpose_add, Matrix.transpose_vecMulVec]
  have hKt : Kᵀ = -K := by
    simp only [K, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
    abel
  change (1 + (c - 1) • P + s • K)ᵀ * (1 + (c - 1) • P + s • K) = 1
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hPt, hKt,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hPP, hPK, hKP, hKK,
    smul_neg, neg_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  have hcoef : (c - 1) * (c - 1) + 2 * (c - 1) + s * s = 0 := by nlinarith
  linear_combination hcoef * P i j

/-- A plane rotation acts by `x ↦ x + (c − 1)((u·x) u + (v·x) v) + s ((v·x) u − (u·x) v)`:
on the plane, `u ↦ c u − s v` and `v ↦ s u + c v`; the orthogonal complement is fixed.
Golub–Van Loan 2013, §5.1.8. -/
theorem planeRotation_mulVec (u v x : n → ℝ) (c s : ℝ) :
    planeRotation u v c s *ᵥ x = x +
      (c - 1) • ((u ⬝ᵥ x) • u + (v ⬝ᵥ x) • v) +
      s • ((v ⬝ᵥ x) • u - (u ⬝ᵥ x) • v) := by
  simp only [planeRotation, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

/-- The rational parametrisation `(c, s) = ((1 − t²)/(1 + t²), 2t/(1 + t²))` of the unit circle,
for every real `t`. -/
theorem sq_rational_rotation_coefficients (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end NLAlib

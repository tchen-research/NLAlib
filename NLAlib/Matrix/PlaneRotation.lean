import NLAlib.Matrix.Projections
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Real rotations in a prescribed plane

Explicit rotations of two orthonormal finite real vectors, with rank-two
formulas suitable for scalar differentiation and spectral perturbations.
Source: Schur–Horn variational rederivation, equations (1) and (6), supporting
the atlas result `schur-horn`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real rotation of an orthonormal pair, extended by the identity on its
orthogonal complement. Schur–Horn variational rederivation, equations (1),(6). -/
def planeRotation (u v : n → ℝ) (c s : ℝ) : Matrix n n ℝ :=
  1 + (c - 1) • (Matrix.vecMulVec u u + Matrix.vecMulVec v v) +
    s • (Matrix.vecMulVec u v - Matrix.vecMulVec v u)

/-- An explicit plane rotation is orthogonal whenever its scalar coefficients
lie on the unit circle. Schur–Horn variational rederivation, equations (1),(6). -/
theorem transpose_planeRotation_mul_self (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation u v c s)ᵀ * planeRotation u v c s = 1 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
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

/-- A plane rotation acts by its two scalar coordinates and fixes the
orthogonal complement. Schur–Horn variational rederivation, equations (1),(6). -/
theorem planeRotation_mulVec (u v x : n → ℝ) (c s : ℝ) :
    planeRotation u v c s *ᵥ x = x +
      (c - 1) • ((u ⬝ᵥ x) • u + (v ⬝ᵥ x) • v) +
      s • ((v ⬝ᵥ x) • u - (u ⬝ᵥ x) • v) := by
  simp only [planeRotation, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

/-- The rational unit-circle coefficients provide rotations for every real
parameter, including zero. Schur–Horn variational rederivation, step (2). -/
theorem sq_rational_rotation_coefficients (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end NLAlib

import NLAlib.Matrix.Inequalities.PlaneRotation
/-!
# Spectral effect of a real plane rotation

Rotating two orthonormal eigenvectors with disjoint coordinate supports gives
an exact linear diagonal increment. Source: Schur–Horn variational rederivation,
equation (6), supporting the atlas result `schur-horn`.
-/
noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating a symmetric matrix by a rotation of two of its eigenvectors
changes only their two-dimensional spectral block. Schur–Horn variational
rederivation, equation (6); no restriction on signed or repeated eigenvalues. -/
theorem planeRotation_mul_mul_transpose_of_eigenvectors
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (α β : ℝ) (hAu : A *ᵥ u = α • u) (hAv : A *ᵥ v = β • v)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    planeRotation u v c s * A * (planeRotation u v c s)ᵀ =
      A + (s ^ 2 * (β - α)) • (Matrix.vecMulVec u u - Matrix.vecMulVec v v) +
        (c * s * (β - α)) • (Matrix.vecMulVec u v + Matrix.vecMulVec v u) := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  have huA : u ᵥ* A = α • u := by rw [← Matrix.mulVec_transpose, hA, hAu]
  have hvA : v ᵥ* A = β • v := by rw [← Matrix.mulVec_transpose, hA, hAv]
  simp only [planeRotation, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, huA, hvA, hAu, hAv,
    Matrix.vecMulVec_smul, smul_smul,
    Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    hu, hv, huv, hvu, zero_smul, one_smul,
    smul_zero, zero_add, add_zero, sub_zero, zero_sub, smul_neg]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (α * u i * u j + β * v i * v j) * hcs

/-- The diagonal increment from rotating eigenvectors with disjoint coordinate
supports is exactly `s²(β-α)(uᵢ²-vᵢ²)`. Schur–Horn variational rederivation,
equation (6), including repeated and negative eigenvalues. -/
theorem planeRotation_mul_mul_transpose_apply_diag_of_disjoint_eigenvectors
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (α β : ℝ) (hAu : A *ᵥ u = α • u) (hAv : A *ᵥ v = β • v)
    (hdisjoint : ∀ i, u i * v i = 0) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (i : n) :
    (planeRotation u v c s * A * (planeRotation u v c s)ᵀ) i i =
      A i i + s ^ 2 * (β - α) * (u i ^ 2 - v i ^ 2) := by
  rw [planeRotation_mul_mul_transpose_of_eigenvectors A hA u v hu hv huv α β hAu hAv c s hcs]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, hdisjoint i, mul_comm (v i) (u i),
    add_zero, mul_zero, pow_two]

end NLAlib

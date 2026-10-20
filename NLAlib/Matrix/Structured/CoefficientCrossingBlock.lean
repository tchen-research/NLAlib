import NLAlib.Matrix.Structured.CoefficientBlockCompression

/-!
# Actual mixed covariance compression for crossed coefficient blocks

The rectangular block with entries `B_j V A_i` is an explicit compression
of a coordinate swap by the two genuine coefficient vectorizations. A
Kronecker amplification of `Vᵀ` supplies the middle factor. Its native
spectral norm therefore costs precisely the two covariance factors.

Source: the alignment estimate in arXiv:2108.06312v2, Proposition 4.6.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Kronecker

namespace NLAlib

variable {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq d]

/-- The actual mixed coefficient block, with fixed order `B_j V A_i`.
The families may have different finite index types. -/
def coefficientCrossingBlock (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (V : Matrix d d ℂ) : Matrix (ι × d) (κ × d) ℂ :=
  fun ia jb => (B jb.1*V*A ia.1) ia.2 jb.2

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- The actual mixed block is a coordinate-swap compression with a genuine
Kronecker middle factor. No orthogonalization of the coefficient families
or Gaussian representation is assumed. -/
theorem coefficientCrossingBlock_eq_covariance_compression
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (V : Matrix d d ℂ) :
    coefficientCrossingBlock A B V =
      (coefficientCovarianceLift A)ᴴ *
        (((1 : Matrix d d ℂ) ⊗ₖ Vᵀ) ⊗ₖ (1 : Matrix d d ℂ)) *
          coefficientCovarianceSwap.permMatrix ℂ * coefficientCovarianceLift B := by
  simp only [Matrix.mul_assoc]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext ia jb
  simp [coefficientCrossingBlock,coefficientCovarianceLift,coefficientVectorization,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Matrix.one_apply,Fintype.sum_prod_type,coefficientCovarianceSwap,
    apply_ite,ite_mul,(hA _).apply,mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- The actual vectorized-coefficient lift has norm at most the norm of the
original vectorization, including empty matrix dimension. -/
theorem specNorm_coefficientCovarianceLift_le (A : ι → Matrix d d ℂ) :
    specNorm (coefficientCovarianceLift A)≤specNorm (coefficientVectorization A) := by
  rw [coefficientCovarianceLift,specNorm_kronecker]
  exact mul_le_of_le_one_right (specNorm_nonneg _) specNorm_one_le

open scoped Matrix.Norms.L2Operator in
/-- A double finite identity amplification of an arbitrary transpose has
norm at most the original matrix norm, with all empty cases retained. -/
theorem specNorm_kronecker_one_transpose_one_le (V : Matrix d d ℂ) :
    specNorm (((1 : Matrix d d ℂ) ⊗ₖ Vᵀ) ⊗ₖ (1 : Matrix d d ℂ))≤specNorm V := by
  rw [specNorm_kronecker,specNorm_kronecker,specNorm_transpose]
  calc
    _ ≤ (1*specNorm V)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right specNorm_one_le (specNorm_nonneg V))
      specNorm_one_le (specNorm_nonneg _)
      (mul_nonneg zero_le_one (specNorm_nonneg V))
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- The genuine mixed crossing block is controlled by the actual two
coefficient vectorization norms and the middle spectral norm. This is
the covariance half of the source alignment estimate. -/
theorem specNorm_coefficientCrossingBlock_le
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (V : Matrix d d ℂ) :
    specNorm (coefficientCrossingBlock A B V)≤
      specNorm (coefficientVectorization A)*specNorm V*specNorm (coefficientVectorization B) := by
  let LA := coefficientCovarianceLift A
  let LB := coefficientCovarianceLift B
  let T := (((1 : Matrix d d ℂ) ⊗ₖ Vᵀ) ⊗ₖ (1 : Matrix d d ℂ))
  let P := (coefficientCovarianceSwap (d := d)).permMatrix ℂ
  have hLA : specNorm LA≤specNorm (coefficientVectorization A) :=
    specNorm_coefficientCovarianceLift_le A
  have hLB : specNorm LB≤specNorm (coefficientVectorization B) :=
    specNorm_coefficientCovarianceLift_le B
  have hT : specNorm T≤specNorm V := specNorm_kronecker_one_transpose_one_le V
  have hP : specNorm P≤1 := Matrix.permMatrix_l2_opNorm_le _
  rw [coefficientCrossingBlock_eq_covariance_compression A B hA V]
  change specNorm (LAᴴ*T*P*LB)≤_
  calc
    _ ≤ specNorm (LAᴴ*T*P)*specNorm LB := specNorm_mul_le _ _
    _ ≤ ((specNorm LAᴴ*specNorm T)*specNorm P)*specNorm LB := by
      exact mul_le_mul_of_nonneg_right
        ((specNorm_mul_le (LAᴴ*T) P).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le LAᴴ T) (specNorm_nonneg P)))
        (specNorm_nonneg LB)
    _ ≤ ((specNorm (coefficientVectorization A)*specNorm V)*1)*
        specNorm (coefficientVectorization B) := by
      rw [specNorm_conjTranspose]
      have hbase := mul_le_mul hLA hT (specNorm_nonneg T)
        (specNorm_nonneg (coefficientVectorization A))
      have hmid := mul_le_mul hbase hP (specNorm_nonneg P)
        (mul_nonneg (specNorm_nonneg (coefficientVectorization A)) (specNorm_nonneg V))
      exact mul_le_mul hmid hLB (specNorm_nonneg LB)
        (mul_nonneg
          (mul_nonneg (specNorm_nonneg (coefficientVectorization A)) (specNorm_nonneg V))
          zero_le_one)
    _ = _ := by ring

/-- The actual coefficient vectorization norm is the square root of its
actual entry-covariance norm. -/
theorem specNorm_coefficientVectorization_eq_sqrt_covariance
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientVectorization A)=Real.sqrt (specNorm (coefficientCovariance A)) := by
  rw [coefficientCovariance,specNorm_mul_conjTranspose_self,Real.sqrt_sq (specNorm_nonneg _)]

end NLAlib

end

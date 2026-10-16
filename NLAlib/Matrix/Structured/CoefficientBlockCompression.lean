import NLAlib.Matrix.Structured.CoefficientBlock

/-! # Two actual swap compressions of the coefficient block

Swapping the coefficient labels gives the variance bound. Swapping the
first and third vectorization coordinates gives the covariance bound.
These are literal finite permutation matrices, so the operator-norm bounds
follow without assuming positivity of the coefficient block.
Source: Bandeira et al. (2026), Propositions 1.3–1.4; finite route (F24).
-/
noncomputable section
open Matrix Finset
open scoped Matrix Kronecker
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

/-- Exchange the two coefficient labels and retain the vector coordinate. -/
def coefficientVarianceSwap : Equiv.Perm (ι × (ι × d)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the first and third of three ordinary vector coordinates. -/
def coefficientCovarianceSwap : Equiv.Perm ((d × d) × d) where
  toFun x := ((x.2, x.1.2), x.1.1)
  invFun x := ((x.2, x.1.2), x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The variance lift applies every coefficient to every input block. -/
def coefficientVarianceLift (A : ι → Matrix d d ℂ) : Matrix (ι × (ι × d)) (ι × d) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ coefficientStack A

/-- The covariance lift is the actual vectorized-coefficient matrix tensored
with an ordinary finite identity matrix. -/
def coefficientCovarianceLift (A : ι → Matrix d d ℂ) : Matrix ((d × d) × d) (ι × d) ℂ :=
  coefficientVectorization A ⊗ₖ (1 : Matrix d d ℂ)

/-- Literal variance swap compression, proved entrywise in finite coordinates. -/
theorem coefficientBlock_eq_variance_swap_compression (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlock A = (coefficientVarianceLift A)ᴴ *
      coefficientVarianceSwap.permMatrix ℂ * coefficientVarianceLift A := by
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
  ext ic je
  simp [coefficientBlock, coefficientVarianceLift, coefficientStack,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, coefficientVarianceSwap,
    apply_ite, ite_mul, (hA _).apply]

omit [Fintype ι] [DecidableEq ι] in
/-- Literal covariance swap compression. The first/third-coordinate swap is
the exact finite operator in the covariance proof, not an assumed factorization.
Source: Bandeira et al. (2026), Proposition 1.4; finite route (F24).
atlas: coefficient-block-partial-transpose (partial) -/
theorem coefficientBlock_eq_covariance_swap_compression (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlock A = (coefficientCovarianceLift A)ᴴ *
      coefficientCovarianceSwap.permMatrix ℂ * coefficientCovarianceLift A := by
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
  ext ic je
  simp [coefficientBlock, coefficientCovarianceLift, coefficientVectorization,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, coefficientCovarianceSwap,
    apply_ite, (hA _).apply, mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- Compressing an actual finite coordinate permutation costs at most the
squared norm of the supplied rectangular factor. -/
theorem specNorm_conjTranspose_permMatrix_mul_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℂ) (σ : Equiv.Perm m) :
    specNorm (Fᴴ * σ.permMatrix ℂ * F) ≤ specNorm F ^ 2 := by
  have hP : specNorm (σ.permMatrix ℂ) ≤ 1 := Matrix.permMatrix_l2_opNorm_le σ
  calc
    _ ≤ specNorm (Fᴴ * σ.permMatrix ℂ) * specNorm F := specNorm_mul_le _ _
    _ ≤ (specNorm Fᴴ * specNorm (σ.permMatrix ℂ)) * specNorm F :=
      mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (specNorm F * 1) * specNorm F := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP (specNorm_nonneg F)) (specNorm_nonneg F)
    _ = _ := by ring

/-- Actual covariance norm bound, valid for arbitrary Hermitian coefficients.
Source: Bandeira et al. (2026), Proposition 1.4.
atlas: coefficient-block-partial-transpose (partial) -/
theorem specNorm_coefficientBlock_le_covariance [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientCovariance A) := by
  open scoped Matrix.Norms.L2Operator in
    have hI : specNorm (1 : Matrix d d ℂ) = 1 := by simp [specNorm_eq_norm]
  rw [coefficientBlock_eq_covariance_swap_compression A hA]
  calc
    _ ≤ specNorm (coefficientCovarianceLift A) ^ 2 :=
      specNorm_conjTranspose_permMatrix_mul_le _ _
    _ = specNorm (coefficientVectorization A) ^ 2 := by
      rw [coefficientCovarianceLift, specNorm_kronecker, hI, mul_one]
    _ = _ := by rw [coefficientCovariance, specNorm_mul_conjTranspose_self]

/-- Actual variance norm bound, obtained by a coefficient-label swap.
Source: Bandeira et al. (2026), Proposition 1.3.
atlas: coefficient-block-partial-transpose (partial) -/
theorem specNorm_coefficientBlock_le_variance [Nonempty ι]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientVariance A) := by
  open scoped Matrix.Norms.L2Operator in
    have hI : specNorm (1 : Matrix ι ι ℂ) = 1 := by simp [specNorm_eq_norm]
  rw [coefficientBlock_eq_variance_swap_compression A hA]
  calc
    _ ≤ specNorm (coefficientVarianceLift A) ^ 2 :=
      specNorm_conjTranspose_permMatrix_mul_le _ _
    _ = specNorm (coefficientStack A) ^ 2 := by
      rw [coefficientVarianceLift, specNorm_kronecker, hI, one_mul]
    _ = _ := by
      rw [← coefficientStack_gram A hA]
      exact specNorm_sq_eq_specNorm_conjTranspose_mul_self _

end NLAlib

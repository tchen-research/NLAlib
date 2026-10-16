import NLAlib.Matrix.Structured.CoefficientBlock
import NLAlib.Matrix.Spectral.TensorExtremeEigenvalues

/-! # Tensor amplification of the actual coefficient block

Associating the finite product coordinates identifies the amplified block
matrix with the tensor product of the original block and an identity.
Source: Bandeira et al. (2026), §1.1, amplification invariance.
-/
noncomputable section
open scoped Matrix Kronecker
namespace NLAlib
variable {ι d r : Type*} [Fintype ι] [Fintype d] [Fintype r]
variable [DecidableEq ι] [DecidableEq d] [DecidableEq r]

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
/-- The amplified coefficient block is literally `C ⊗ I`, up to the canonical
association of the three finite coordinate labels. -/
theorem coefficientBlock_kronecker_one (A : ι → Matrix d d ℂ) :
    coefficientBlock (fun i => A i ⊗ₖ (1 : Matrix r r ℂ)) =
      (coefficientBlock A ⊗ₖ (1 : Matrix r r ℂ)).reindex
        (Equiv.prodAssoc ι d r) (Equiv.prodAssoc ι d r) := by
  ext ic je
  simp only [coefficientBlock, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    Matrix.kroneckerMap_apply]

/-- Actual identity amplification of every Hermitian coefficient preserves the
largest eigenvalue of the coefficient block, even when the block is indefinite. -/
theorem lambdaMax_coefficientBlock_kronecker_one [Nonempty r]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    lambdaMax (coefficientBlock (fun i => A i ⊗ₖ (1 : Matrix r r ℂ))) =
      lambdaMax (coefficientBlock A) := by
  rw [coefficientBlock_kronecker_one, lambdaMax_reindex,
    lambdaMax_kronecker_one (isHermitian_coefficientBlock A hA)]

/-- Tensoring the actual coefficients with any nonempty finite identity leaves
the source parameter unchanged. The proof preserves the largest eigenvalue,
rather than replacing it by the spectral norm of an indefinite block.
Source: Bandeira et al. (2026), §1.1, amplification invariance.
atlas: coefficient-block-partial-transpose (partial) -/
theorem coefficientBlockKappa_kronecker_one [Nonempty r]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa (fun i => A i ⊗ₖ (1 : Matrix r r ℂ)) = coefficientBlockKappa A := by
  rw [coefficientBlockKappa, coefficientBlockKappa, lambdaMax_coefficientBlock_kronecker_one A hA]

end NLAlib

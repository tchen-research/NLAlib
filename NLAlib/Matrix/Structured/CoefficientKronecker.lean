import NLAlib.Matrix.Structured.CoefficientBlock

/-! # Covariance of genuine tensor coefficient families

Variance and unnormalized entry covariance factor exactly for all finite
Kronecker coefficient families. The entry-coordinate reindexing is explicit;
these identities preserve the true Frobenius vectorization normalization.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker
namespace NLAlib
variable {ι κ d n : Type*} [Fintype ι] [Fintype κ] [Fintype d] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq d] [DecidableEq n]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq d] [DecidableEq n] in
/-- The variance of an actual product-indexed Kronecker coefficient family
is the Kronecker product of the two actual variance matrices. -/
theorem coefficientVariance_kronecker
    (A : ι → Matrix d d ℂ) (B : κ → Matrix n n ℂ) :
    coefficientVariance (fun ik : ι×κ => A ik.1⊗ₖB ik.2) =
      coefficientVariance A⊗ₖcoefficientVariance B := by
  ext ab ce
  simp only [coefficientVariance,Matrix.sum_apply,Fintype.sum_prod_type,
    ← Matrix.mul_kronecker_mul,Matrix.kroneckerMap_apply,Finset.sum_mul_sum]

omit [Fintype d] [Fintype n] [DecidableEq ι] [DecidableEq κ] [DecidableEq d] [DecidableEq n] in
/-- The full entry covariance of genuine tensor coefficients factors after
the explicit swap of the two middle entry-coordinate indices. -/
theorem coefficientCovariance_kronecker_reindex
    (A : ι → Matrix d d ℂ) (B : κ → Matrix n n ℂ) :
    (coefficientCovariance (fun ik : ι×κ => A ik.1⊗ₖB ik.2)).reindex
      (Equiv.prodProdProdComm d n d n) (Equiv.prodProdProdComm d n d n) =
        coefficientCovariance A⊗ₖcoefficientCovariance B := by
  ext abrs cetu
  simp only [coefficientCovariance,coefficientVectorization,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.prodProdProdComm_symm,Equiv.prodProdProdComm_apply,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,star_mul,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] [DecidableEq κ] in
open scoped Matrix.Norms.L2Operator in
/-- Genuine entry-covariance spectral norms multiply under a product-indexed
Kronecker coefficient family, with the unnormalized vectorization geometry. -/
theorem specNorm_coefficientCovariance_kronecker
    (A : ι → Matrix d d ℂ) (B : κ → Matrix n n ℂ) :
    specNorm (coefficientCovariance (fun ik : ι×κ => A ik.1⊗ₖB ik.2)) =
      specNorm (coefficientCovariance A)*specNorm (coefficientCovariance B) := by
  rw [← specNorm_reindex _ (Equiv.prodProdProdComm d n d n)
    (Equiv.prodProdProdComm d n d n),coefficientCovariance_kronecker_reindex,
    specNorm_kronecker]

omit [DecidableEq ι] [DecidableEq κ] in
open scoped Matrix.Norms.L2Operator in
/-- Genuine variance spectral norms multiply under a product-indexed
Kronecker coefficient family. This includes empty coefficient families. -/
theorem specNorm_coefficientVariance_kronecker
    (A : ι → Matrix d d ℂ) (B : κ → Matrix n n ℂ) :
    specNorm (coefficientVariance (fun ik : ι×κ => A ik.1⊗ₖB ik.2)) =
      specNorm (coefficientVariance A)*specNorm (coefficientVariance B) := by
  rw [coefficientVariance_kronecker,specNorm_kronecker]

end NLAlib

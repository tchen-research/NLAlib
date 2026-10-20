import NLAlib.RandomMatrix.Gaussian.Basic.GUECoefficientMatrices
import NLAlib.Matrix.Structured.CoefficientKronecker

/-! # True variance and entry covariance of the finite-N input

The source parameters are computed from the actual independent real GUE
coefficient matrices and the actual diagonal coordinate matrices. No matrix
covariance law or norm formula is supplied as a hypothesis.
Source: arXiv:2108.06312v2, Lemma 5.5.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker
namespace NLAlib
variable {n d ι : Type*} [Fintype n] [Fintype d] [Fintype ι]
  [DecidableEq n] [DecidableEq d] [DecidableEq ι]

/-- The true independent-real-coordinate GUE entry covariance is precisely
the inverse ensemble dimension times the full entry-coordinate identity. -/
theorem coefficientCovariance_gueCoefficientMatrix :
    coefficientCovariance (gueCoefficientMatrix (n := n)) =
      (Fintype.card n : ℝ)⁻¹ • (1 : Matrix (n×n) (n×n) ℂ) := by
  ext rs tu
  simp only [coefficientCovariance,coefficientVectorization,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have hs (k : GUECoordinate Unit n) : star (gueCoefficientMatrix k tu.1 tu.2) =
      gueCoefficientMatrix k tu.2 tu.1 := by
    exact (gueCoefficientMatrix_isHermitian k).apply _ _
  simp_rw [hs]
  rw [sum_gueCoefficientMatrix_entry_mul]
  by_cases h : rs=tu
  · subst tu
    simp
  · have hh : ¬(rs.1=tu.1 ∧ rs.2=tu.2) := fun he => h (Prod.ext he.1 he.2)
    simp [hh,h]

open scoped Matrix.Norms.L2Operator in
/-- The true GUE entry-covariance norm is exactly the inverse ensemble
dimension. The empty ensemble has both sides zero. -/
theorem specNorm_coefficientCovariance_gueCoefficientMatrix :
    specNorm (coefficientCovariance (gueCoefficientMatrix (n := n))) =
      (Fintype.card n : ℝ)⁻¹ := by
  rw [coefficientCovariance_gueCoefficientMatrix]
  rcases isEmpty_or_nonempty n with hn|hn
  · let := hn
    simp [Fintype.card_eq_zero,specNorm_zero]
  · let := hn
    rw [specNorm_eq_norm,norm_smul,norm_one,mul_one,Real.norm_of_nonneg (by positivity)]

/-- The actual GUE coefficient variance is the identity, with the true
normalization of the native Gaussian ensemble. -/
theorem coefficientVariance_gueCoefficientMatrix :
    coefficientVariance (gueCoefficientMatrix (n := n)) = (1 : Matrix n n ℂ) :=
  sum_gueCoefficientMatrix_sq_eq_one

/-- The actual diagonal coordinate coefficient variance is the identity. -/
theorem coefficientVariance_diagonal_single :
    coefficientVariance (fun a : n => (Matrix.single a a 1 : Matrix n n ℂ)) = 1 := by
  simpa only [coefficientVariance,Matrix.single_mul_single_same,one_mul] using
    (Matrix.sum_single_one (m := n) (α := ℂ))

open scoped Matrix.Norms.L2Operator in
/-- The true unnormalized entry covariance of independent diagonal Gaussian
coordinates is an orthogonal projection, so its norm is at most one. -/
theorem specNorm_coefficientCovariance_diagonal_single_le_one :
    specNorm (coefficientCovariance
      (fun a : n => (Matrix.single a a 1 : Matrix n n ℂ))) ≤ 1 := by
  let V := coefficientVectorization (fun a : n => (Matrix.single a a 1 : Matrix n n ℂ))
  have hV : Vᴴ*V=(1 : Matrix n n ℂ) := by
    ext a b
    by_cases hab : a=b <;>
      simp [V,coefficientVectorization,Matrix.mul_apply,Fintype.sum_prod_type,
        Matrix.single_apply,ite_and,hab,Matrix.one_apply]
  have hb : specNorm V≤1 := specNorm_le_one_of_orthonormal hV
  change specNorm (V*Vᴴ)≤1
  rw [specNorm_mul_conjTranspose_self]
  nlinarith [specNorm_nonneg V]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Tensoring an arbitrary actual coefficient family with the true GUE
coordinates divides its genuine entry covariance norm by the ensemble
dimension. All empty dimensions are included. -/
theorem specNorm_coefficientCovariance_kronecker_gueCoefficientMatrix
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientCovariance
      (fun ik : ι×GUECoordinate Unit n => A ik.1⊗ₖgueCoefficientMatrix ik.2)) =
        specNorm (coefficientCovariance A)/(Fintype.card n : ℝ) := by
  rw [specNorm_coefficientCovariance_kronecker,
    specNorm_coefficientCovariance_gueCoefficientMatrix,div_eq_mul_inv]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Tensoring with the true diagonal Gaussian coordinates never increases
the original unnormalized entry-covariance norm. -/
theorem specNorm_coefficientCovariance_kronecker_diagonal_single_le
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientCovariance
      (fun ia : ι×n => A ia.1⊗ₖ(Matrix.single ia.2 ia.2 1 : Matrix n n ℂ))) ≤
        specNorm (coefficientCovariance A) := by
  rw [specNorm_coefficientCovariance_kronecker A
    (fun a : n => (Matrix.single a a 1 : Matrix n n ℂ))]
  exact mul_le_of_le_one_right (specNorm_nonneg _)
    specNorm_coefficientCovariance_diagonal_single_le_one

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The true finite-N GUE tensor coefficient variance is bounded by the
original variance, uniformly in the ensemble dimension. -/
theorem specNorm_coefficientVariance_kronecker_gueCoefficientMatrix_le
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientVariance
      (fun ik : ι×GUECoordinate Unit n => A ik.1⊗ₖgueCoefficientMatrix ik.2)) ≤
        specNorm (coefficientVariance A) := by
  rw [specNorm_coefficientVariance_kronecker,coefficientVariance_gueCoefficientMatrix]
  exact mul_le_of_le_one_right (specNorm_nonneg _) specNorm_one_le

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The true diagonal tensor coefficient variance is bounded by the original
variance, uniformly in the ensemble dimension. -/
theorem specNorm_coefficientVariance_kronecker_diagonal_single_le
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientVariance
      (fun ia : ι×n => A ia.1⊗ₖ(Matrix.single ia.2 ia.2 1 : Matrix n n ℂ))) ≤
        specNorm (coefficientVariance A) := by
  rw [specNorm_coefficientVariance_kronecker A
    (fun a : n => (Matrix.single a a 1 : Matrix n n ℂ)),coefficientVariance_diagonal_single]
  exact mul_le_of_le_one_right (specNorm_nonneg _) specNorm_one_le

end NLAlib

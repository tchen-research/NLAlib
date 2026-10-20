import NLAlib.RandomMatrix.Gaussian.Basic.GUE
import NLAlib.Matrix.Basic.NormalizedTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

/-!
# Actual real-coordinate GUE coefficient matrices

The matrices below are obtained by evaluating the actual normalized GUE map
on the standard real coordinate vectors. Their exact covariance and square
sum are therefore properties of the existing genuine Gaussian ensemble.
No abstract covariance replacement or basis specification is assumed.

Source: arXiv:2108.06312v2, Sections 5.1 and 6.1.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual coefficient matrices of the normalized one-color GUE map in its
independent real Gaussian coordinates. -/
def gueCoefficientMatrix (k : GUECoordinate Unit n) : Matrix n n ℂ :=
  gueMatrix (Pi.single k 1) ()

/-- Each real-coordinate coefficient of the actual GUE map is Hermitian. -/
theorem gueCoefficientMatrix_isHermitian (k : GUECoordinate Unit n) :
    (gueCoefficientMatrix k).IsHermitian :=
  gueMatrix_isHermitian _ _

/-- The actual basis-matrix entry is the existing public GUE entry
coefficient in precisely the same independent coordinate. -/
theorem gueCoefficientMatrix_apply (k : GUECoordinate Unit n) (a b : n) :
    gueCoefficientMatrix k a b = gueEntryCoefficient () a b k := by
  rw [gueCoefficientMatrix,gueMatrix_apply_eq_complexGaussianLinearForm]
  unfold complexGaussianLinearForm
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

/-- The actual GUE is exactly the finite real-coordinate series in these
actual Hermitian coefficients. -/
theorem gueMatrix_eq_sum_coordinate_smul_coefficient
    (x : GUECoordinate Unit n → ℝ) :
    gueMatrix x () = ∑ k, (x k : ℂ) • gueCoefficientMatrix k := by
  ext a b
  simp only [gueMatrix_apply_eq_complexGaussianLinearForm,complexGaussianLinearForm,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,gueCoefficientMatrix_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact complex bilinear covariance of the actual GUE coefficient entries,
including every repeated or diagonal entry. The entry indices themselves
supply nonempty matrix dimension. -/
theorem sum_gueCoefficientMatrix_entry_mul (a b c e : n) :
    (∑ k, gueCoefficientMatrix k a b*gueCoefficientMatrix k c e) =
      if a=e ∧ b=c then (Fintype.card n : ℂ)⁻¹ else 0 := by
  let : Nonempty n := ⟨a⟩
  have h := integral_gueMatrix_entry_mul (c := Unit) () () a b c e
  simp_rw [gueMatrix_apply_eq_complexGaussianLinearForm] at h
  rw [integral_complexGaussianLinearForm_mul] at h
  simpa [dotProduct,gueCoefficientMatrix_apply] using h

/-- The actual independent real-coordinate GUE coefficients have square sum
equal to the actual identity matrix, including empty dimension. -/
theorem sum_gueCoefficientMatrix_sq_eq_one :
    (∑ k : GUECoordinate Unit n, gueCoefficientMatrix k*gueCoefficientMatrix k) =
      (1 : Matrix n n ℂ) := by
  ext a b
  let : Nonempty n := ⟨a⟩
  have hN : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Matrix.sum_apply,Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [sum_gueCoefficientMatrix_entry_mul]
  by_cases hab : a=b
  · subst b
    simp [hN]
  · simp [hab]

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- GUE covariance agrees with the diagonal covariance on a genuine tensor
matrix with identity in the ensemble coordinate. This is the exact native
cancellation mechanism used in source Corollary 5.3 and Lemma 6.2. -/
theorem sum_kronecker_gueCoefficientMatrix_sandwich_identity
    (A Q : Matrix d d ℂ) :
    (∑ k : GUECoordinate Unit n,
      (A⊗ₖgueCoefficientMatrix k)*(Q⊗ₖ(1 : Matrix n n ℂ))*
        (A⊗ₖgueCoefficientMatrix k)) = (A*Q*A)⊗ₖ(1 : Matrix n n ℂ) := by
  simp only [← Matrix.mul_kronecker_mul,Matrix.mul_one]
  ext ab ce
  have h := congrFun (congrFun
    (sum_gueCoefficientMatrix_sq_eq_one (n := n)) ab.2) ce.2
  simp only [Matrix.sum_apply] at h
  simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply,← Finset.mul_sum,h]

omit [DecidableEq d] in
/-- The actual diagonal Gaussian coordinate matrices have the same identity
sandwich action as the normalized GUE coordinates. -/
theorem sum_kronecker_diagonal_sandwich_identity (A Q : Matrix d d ℂ) :
    (∑ a : n, (A⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))*
      (Q⊗ₖ(1 : Matrix n n ℂ))*(A⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))) =
        (A*Q*A)⊗ₖ(1 : Matrix n n ℂ) := by
  have hs : (∑ a : n, (Matrix.single a a 1 : Matrix n n ℂ)*Matrix.single a a 1) = 1 := by
    simpa only [Matrix.single_mul_single_same,one_mul] using
      (Matrix.sum_single_one (m := n) (α := ℂ))
  simp only [← Matrix.mul_kronecker_mul,Matrix.mul_one]
  ext ab ce
  have h := congrFun (congrFun hs ab.2) ce.2
  simp only [Matrix.sum_apply] at h
  simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply,← Finset.mul_sum,h]

omit [DecidableEq d] in
/-- Exact cancellation between the two genuine finite-N covariance
families on an actual tensor matrix with identity ensemble coordinate.
Source: arXiv:2108.06312v2, Corollary 5.3 and Lemma 6.2. -/
theorem sum_diagonal_sub_gue_covariance_sandwich_identity
    {ι : Type*} [Fintype ι] (A : ι → Matrix d d ℂ) (Q : Matrix d d ℂ) :
    (∑ i, ∑ a : n, (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))*
      (Q⊗ₖ(1 : Matrix n n ℂ))*(A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))) -
    (∑ i, ∑ k : GUECoordinate Unit n,
      (A i⊗ₖgueCoefficientMatrix k)*(Q⊗ₖ(1 : Matrix n n ℂ))*
        (A i⊗ₖgueCoefficientMatrix k)) = 0 := by
  simp_rw [sum_kronecker_diagonal_sandwich_identity,
    sum_kronecker_gueCoefficientMatrix_sandwich_identity]
  exact sub_self _

end NLAlib

end

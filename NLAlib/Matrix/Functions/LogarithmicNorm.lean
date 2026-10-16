import NLAlib.Matrix.Functions.ExponentialEnergy
import NLAlib.Matrix.Functions.HermitianCalculus
import NLAlib.Matrix.Inequalities.AccretiveKernels

/-!
# Logarithmic norm of a complex matrix

The largest eigenvalue of the native self-adjoint part controls the
exponential semigroup. The real energy form is connected explicitly to
Loewner order. Higham, Functions of Matrices; toolkit derivations,
Section `eq-lognorm`.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Euclidean energy form equals the real part of the matrix
quadratic form, with the library's standard vector identification. -/
theorem real_inner_toEuclideanLin (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    inner ℝ x (A.toEuclideanLin x) = (quadForm A x.ofLp).re := by
  simp only [PiLp.inner_apply, quadForm, dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  convert! real_inner_eq_re_inner ℂ (x.ofLp i) ((A *ᵥ x.ofLp) i) using 1
  simp only [RCLike.inner_apply, mul_comm]
  rfl

/-- A Loewner upper bound on the Hermitian part gives the same energy
bound in the underlying real Hilbert space. -/
theorem real_inner_le_of_selfAdjointPart_le {A : Matrix n n ℂ} {c : ℝ}
    (hA : (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ c • 1)
    (x : EuclideanSpace ℂ n) :
    inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2 := by
  have h := (Matrix.le_iff.mp hA).re_quadForm_nonneg x.ofLp
  have he := quadForm_selfAdjointPart A x.ofLp
  have hn : (star x.ofLp ⬝ᵥ x.ofLp).re = ‖x‖ ^ 2 :=
    (norm_toLp_sq_eq_re_star_dotProduct x.ofLp).symm
  rw [real_inner_toEuclideanLin]
  change 0 ≤ (quadForm (c • 1 - (selfAdjointPart ℝ A : Matrix n n ℂ)) x.ofLp).re at h
  simp only [quadForm, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, Complex.sub_re, Complex.real_smul] at h
  change (quadForm A x.ofLp).re ≤ c * ‖x‖ ^ 2
  change 0 ≤ ((c : ℂ) * (star x.ofLp ⬝ᵥ x.ofLp)).re -
    (quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x.ofLp).re at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  change 0 ≤ c * (star x.ofLp ⬝ᵥ x.ofLp).re -
    (quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x.ofLp).re at h
  rw [he, Complex.ofReal_re, hn] at h
  linarith

/-- Every Hermitian-part upper bound is an exponential semigroup bound,
including negative constants and nonnormal matrices.
atlas: matrix-exponential-logarithmic-norm (partial) -/
theorem specNorm_matrixExp_smul_le_of_selfAdjointPart_le
    {A : Matrix n n ℂ} {c : ℝ}
    (hA : (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ c • 1)
    {t : ℝ} (ht : 0 ≤ t) :
    specNorm (matrixExp (t • A)) ≤ Real.exp (t * c) :=
  specNorm_matrixExp_smul_le_of_energy_bound A c (real_inner_le_of_selfAdjointPart_le hA) ht

/-- The logarithmic norm is the largest eigenvalue of the Hermitian part,
using the library's existing extremal-eigenvalue function. -/
def matrixLogarithmicNorm (A : Matrix n n ℂ) : ℝ :=
  lambdaMax (selfAdjointPart ℝ A : Matrix n n ℂ)

/-- The Hermitian part is bounded above by its largest eigenvalue. -/
theorem selfAdjointPart_le_matrixLogarithmicNorm (A : Matrix n n ℂ) :
    (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ matrixLogarithmicNorm A • 1 := by
  have hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian :=
    (selfAdjointPart ℝ A).property
  have h : (selfAdjointPart ℝ A : Matrix n n ℂ) ≤
      algebraMap ℝ (Matrix n n ℂ) (matrixLogarithmicNorm A) :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mpr
      (le_of_mem_spectrum_of_lambdaMax_le _ hH le_rfl)
  simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using h

/-- The matrix logarithmic norm bounds the exponential semigroup.
atlas: matrix-exponential-logarithmic-norm (partial) -/
theorem specNorm_matrixExp_smul_le_exp_logarithmicNorm (A : Matrix n n ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    specNorm (matrixExp (t • A)) ≤ Real.exp (t * matrixLogarithmicNorm A) :=
  specNorm_matrixExp_smul_le_of_selfAdjointPart_le (selfAdjointPart_le_matrixLogarithmicNorm A) ht

end NLAlib

import NLAlib.Matrix.Structured.KroneckerNormRank
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # The partially transposed coefficient Gram matrix

For Hermitian coefficients its blocks are `Cᵢⱼ = Aⱼ Aᵢ`. Two concrete finite
swap compressions give the variance and entry-covariance norm bounds.
This block matrix is Hermitian and can be indefinite; its parameter uses
its largest eigenvalue. Source: Bandeira et al. (2026), §1.1, (7)–(8).
-/
noncomputable section
open Matrix Finset
open scoped Matrix ComplexOrder MatrixOrder Kronecker
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

/-- The coefficient block matrix, with the order `Aⱼ Aᵢ` fixed explicitly. -/
def coefficientBlock (A : ι → Matrix d d ℂ) : Matrix (ι × d) (ι × d) ℂ :=
  fun ic je => (A je.1 * A ic.1) ic.2 je.2

/-- The usual matrix-series variance matrix. -/
def coefficientVariance (A : ι → Matrix d d ℂ) : Matrix d d ℂ := ∑ i, A i * A i

/-- Ordinary column labels for the vectorized coefficient entries. -/
def coefficientVectorization (A : ι → Matrix d d ℂ) : Matrix (d × d) ι ℂ :=
  fun ab i => A i ab.1 ab.2

/-- Entry covariance of the vectorized coefficients. -/
def coefficientCovariance (A : ι → Matrix d d ℂ) : Matrix (d × d) (d × d) ℂ :=
  coefficientVectorization A * (coefficientVectorization A)ᴴ

/-- The nonnegative square root of the largest coefficient-block eigenvalue. -/
def coefficientBlockKappa (A : ι → Matrix d d ℂ) : ℝ := Real.sqrt (lambdaMax (coefficientBlock A))

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- The covariance definition is literally the sum of vectorized outer products. -/
theorem coefficientCovariance_eq_sum_vecMulVec (A : ι → Matrix d d ℂ) :
    coefficientCovariance A = ∑ i,
      vecMulVec (fun ab : d × d => A i ab.1 ab.2)
        (star (fun ab : d × d => A i ab.1 ab.2)) := by
  ext ab ce
  simp [coefficientCovariance, coefficientVectorization, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
/-- Hermitian coefficients give a Hermitian coefficient block, without requiring
pairwise commutation or positivity of the coefficient block. -/
theorem isHermitian_coefficientBlock (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (coefficientBlock A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ic je
  have he : (A ic.1 * A je.1)ᴴ = A je.1 * A ic.1 := by
    rw [Matrix.conjTranspose_mul, (hA ic.1).eq, (hA je.1).eq]
  exact congrFun (congrFun he ic.2) je.2

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
/-- Each diagonal coefficient block is PSD, so every diagonal entry is nonnegative. -/
theorem coefficientBlock_diag_nonneg (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ic : ι × d) : 0 ≤ coefficientBlock A ic ic := by
  have hp : (A ic.1 * A ic.1).PosSemidef := by
    simpa only [(hA ic.1).eq] using Matrix.posSemidef_conjTranspose_mul_self (A ic.1)
  exact hp.diag_nonneg

/-- Nonnegative diagonal blocks force the largest block eigenvalue to be nonnegative.
Source: Bandeira et al. (2026), §1.1.
atlas: coefficient-block-partial-transpose (partial) -/
theorem lambdaMax_coefficientBlock_nonneg [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    0 ≤ lambdaMax (coefficientBlock A) := by
  apply (isHermitian_coefficientBlock A hA).lambdaMax_nonneg_of_trace_re_nonneg
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun ic _ =>
    (Complex.nonneg_iff.mp (coefficientBlock_diag_nonneg A hA ic)).1

/-- Stack the coefficient matrices vertically. -/
def coefficientStack (A : ι → Matrix d d ℂ) : Matrix (ι × d) d ℂ :=
  fun ia b => A ia.1 ia.2 b

omit [DecidableEq ι] [DecidableEq d] in
/-- The actual stacked Gram matrix is exactly the variance matrix. -/
theorem coefficientStack_gram (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (coefficientStack A)ᴴ * coefficientStack A = coefficientVariance A := by
  ext c e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientStack,
    Fintype.sum_prod_type, coefficientVariance, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [(hA i).apply]

end NLAlib

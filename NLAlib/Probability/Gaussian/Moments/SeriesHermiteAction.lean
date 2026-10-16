import NLAlib.Probability.Gaussian.Moments.HermiteAction
import NLAlib.Matrix.Structured.HermiteCompression

/-! # Matrix-series multiplication in the finite Hermite model

Finite Hermite expansions of matrix coefficient arrays intertwine the
literal finite Jacobi matrix with actual multiplication by a Gaussian matrix
series, with explicit degree support below the cutoff.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix Kronecker
namespace NLAlib
variable {ι d c : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d] {p : ℕ}

/-- The actual matrix-valued polynomial represented by a finite coefficient
matrix in the total-degree Hermite basis. -/
def matrixHermiteExpansion (Z : Matrix (d × HermiteIndex ι p) c ℂ) (x : ι → ℝ) :
    Matrix d c ℂ := fun a b => hermiteExpansion (fun α => Z (a, α) b) x

private theorem operator_mul_apply (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (Z : Matrix (d × HermiteIndex ι p) c ℂ)
    (a : d) (α : HermiteIndex ι p) (b : c) :
    (hermiteSeriesOperator A p * Z) (a, α) b =
      ∑ i, ∑ j, A i a j *
        ((hermiteCreation p i + (hermiteCreation p i)ᴴ) *ᵥ
          (fun β => Z (j, β) b)) α := by
  rw [hermiteSeriesOperator_eq_sum_kronecker A hA]
  simp only [Finset.sum_mul, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- The matrix Hermite model represents multiplication by the actual
Hermitian Gaussian series on coefficient arrays below the cutoff. -/
theorem matrixHermiteExpansion_operator_mul
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (Z : Matrix (d × HermiteIndex ι p) c ℂ)
    (hZ : ∀ a α b, ¬ α.degree < p → Z (a, α) b = 0) (x : ι → ℝ) :
    matrixHermiteExpansion (hermiteSeriesOperator A p * Z) x =
      (∑ i, x i • A i) * matrixHermiteExpansion Z x := by
  ext a b
  simp only [matrixHermiteExpansion, operator_mul_apply A hA]
  simp_rw [hermiteExpansion_sum, hermiteExpansion_const_mul]
  have hterm (i : ι) (j : d) :
      hermiteExpansion ((hermiteCreation p i + (hermiteCreation p i)ᴴ) *ᵥ
        (fun β => Z (j, β) b)) x =
      (x i : ℂ) * hermiteExpansion (fun β => Z (j, β) b) x :=
    hermiteExpansion_creation_add_conjTranspose_mulVec i _
      (fun α hα => hZ j α b hα) x
  simp_rw [hterm]
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, matrixHermiteExpansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [RCLike.real_smul_eq_coe_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  rfl

/-- Finite matrix-series multiplication increases Hermite degree support by
at most one, for the actual finite Jacobi matrix. -/
theorem hermiteSeriesOperator_mul_support
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (Z : Matrix (d × HermiteIndex ι p) c ℂ) (k : ℕ)
    (hZ : ∀ a α b, k < α.degree → Z (a, α) b = 0)
    (a : d) (α : HermiteIndex ι p) (b : c) (hα : k + 1 < α.degree) :
    (hermiteSeriesOperator A p * Z) (a, α) b = 0 := by
  rw [operator_mul_apply A hA]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hermiteCreation_add_conjTranspose_mulVec_support i _ k
    (fun β hβ => hZ j β b hβ) α hα, mul_zero]

end NLAlib

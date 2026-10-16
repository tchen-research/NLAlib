import NLAlib.Matrix.Structured.HermiteLadders
import NLAlib.Matrix.Structured.KroneckerOrder
import NLAlib.Matrix.Structured.CoefficientBlock

/-! # Coefficient-block factorization of finite Hermite creation

The covariance term is a congruence of the actual partially transposed
coefficient block. That block need not be positive semidefinite; only its
largest eigenvalue is used by the subsequent bound.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix Kronecker MatrixOrder ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d] {p : ℕ}

/-- The finite creation operator weighted by the actual matrix coefficients. -/
def hermiteSeriesCreation (A : ι → Matrix d d ℂ) (p : ℕ) :
    Matrix (d × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ :=
  ∑ i, A i ⊗ₖ hermiteCreation p i

/-- The self-adjoint finite matrix representing Gaussian matrix-series
multiplication up to the total-degree cutoff. -/
def hermiteSeriesOperator (A : ι → Matrix d d ℂ) (p : ℕ) :
    Matrix (d × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ :=
  hermiteSeriesCreation A p + (hermiteSeriesCreation A p)ᴴ

/-- The finite Hermite multiplication matrix is Hermitian for any coefficient
array, by its creation-plus-adjoint construction. -/
theorem isHermitian_hermiteSeriesOperator (A : ι → Matrix d d ℂ) (p : ℕ) :
    (hermiteSeriesOperator A p).IsHermitian := by
  simp [hermiteSeriesOperator, Matrix.IsHermitian, Matrix.conjTranspose_add, add_comm]

/-- For Hermitian coefficients the finite series multiplication operator is
the sum of each coefficient tensored with its coordinate Jacobi matrix. -/
theorem hermiteSeriesOperator_eq_sum_kronecker
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    hermiteSeriesOperator A p =
      ∑ i, A i ⊗ₖ (hermiteCreation p i + (hermiteCreation p i)ᴴ) := by
  simp only [hermiteSeriesOperator, hermiteSeriesCreation, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_kronecker, (hA _).eq, Matrix.kronecker_add,
    Finset.sum_add_distrib]

/-- Stack the ordinary-coordinate identity tensored with each annihilator.
The row labels match `coefficientBlock A ⊗ I` without any hidden transpose. -/
def hermiteAnnihilatorStack (d : Type*) [Fintype d] [DecidableEq d] (p : ℕ) :
    Matrix ((ι × d) × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ :=
  fun ia b => (if ia.1.2 = b.1 then 1 else 0) *
    (hermiteCreation p ia.1.1)ᴴ ia.2 b.2

/-- Weighted creation vanishes on top-degree input. -/
theorem hermiteSeriesCreation_mul_interior (A : ι → Matrix d d ℂ) :
    hermiteSeriesCreation A p * ((1 : Matrix d d ℂ) ⊗ₖ hermiteInterior p) =
      hermiteSeriesCreation A p := by
  simp only [hermiteSeriesCreation, Finset.sum_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hermiteCreation_mul_interior]

/-- The annihilator stack has exactly the occupation-number Gram matrix. -/
theorem hermiteAnnihilatorStack_gram :
    (hermiteAnnihilatorStack (ι := ι) d p)ᴴ * hermiteAnnihilatorStack d p =
      (1 : Matrix d d ℂ) ⊗ₖ hermiteNumber p := by
  ext a b
  rcases a with ⟨a₀, α⟩
  rcases b with ⟨b₀, β⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hermiteAnnihilatorStack,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases hab : a₀ = b₀
  · subst b₀
    simp only [apply_ite, map_mul, map_one, map_zero, star_star, ite_mul,
      mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [star_zero, ite_self, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hh := congrArg (fun M : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ => M α β)
      (sum_hermiteCreation_mul_conjTranspose (ι := ι) (p := p))
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using hh
  · simp [hab, Ne.symm hab, apply_ite]

/-- Congruence of the actual coefficient block is the noncommutative
creation correction, with the coefficient order fixed by the row labels. -/
theorem hermiteAnnihilatorStack_coefficientBlock (A : ι → Matrix d d ℂ) :
    (hermiteAnnihilatorStack (ι := ι) d p)ᴴ *
        (coefficientBlock A ⊗ₖ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ)) *
        hermiteAnnihilatorStack d p =
      ∑ i, ∑ j, (A i * A j) ⊗ₖ (hermiteCreation p j * (hermiteCreation p i)ᴴ) := by
  ext a b
  rcases a with ⟨a₀, α⟩
  rcases b with ⟨b₀, β⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hermiteAnnihilatorStack,
    coefficientBlock, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Matrix.sum_apply]
  simp only [map_mul, apply_ite, map_one, map_zero, star_star, star_zero,
    ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_one]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_self]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The finite Hermite creation Gram matrix equals variance plus the
coefficient-block congruence on the interior occupation space. -/
theorem hermiteSeriesCreation_gram_mul_interior
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (hermiteSeriesCreation A p)ᴴ * hermiteSeriesCreation A p *
        ((1 : Matrix d d ℂ) ⊗ₖ hermiteInterior p) =
      (coefficientVariance A ⊗ₖ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ) +
        (hermiteAnnihilatorStack (ι := ι) d p)ᴴ *
          (coefficientBlock A ⊗ₖ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ)) *
          hermiteAnnihilatorStack d p) *
            ((1 : Matrix d d ℂ) ⊗ₖ hermiteInterior p) := by
  rw [hermiteAnnihilatorStack_coefficientBlock]
  simp only [hermiteSeriesCreation, Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker,
    (hA _).eq, Finset.sum_mul, Matrix.mul_sum, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  simp_rw [hermiteCreation_commutator, Matrix.add_mul, Matrix.kronecker_add]
  simp only [Matrix.add_mul, Finset.sum_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]
  simp only [Finset.sum_add_distrib]
  congr 1
  ext ⟨a, α⟩ ⟨b, β⟩
  simp [coefficientVariance, Matrix.sum_apply, Matrix.kronecker_apply,
    apply_ite, Finset.sum_mul, Finset.mul_sum]

end NLAlib

import NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A finite Hermitian spanning family from matrix units

Symmetric and imaginary skew matrix units span every complex matrix over
complex coefficients. Their coefficients are differences of four actual
quadratic probes, so scalar positive measures can be polarized directly.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric Hermitian matrix unit. -/
def hermitianUnitRe (i j : n) : Matrix n n ℂ := single i j 1 + single j i 1

/-- The imaginary skew Hermitian matrix unit. -/
def hermitianUnitIm (i j : n) : Matrix n n ℂ := Complex.I • (single i j 1 - single j i 1)

omit [Fintype n] in
/-- Symmetric matrix units are Hermitian, including repeated indices. -/
theorem isHermitian_hermitianUnitRe (i j : n) : (hermitianUnitRe i j).IsHermitian := by
  simp [hermitianUnitRe, Matrix.IsHermitian, add_comm]

omit [Fintype n] in
/-- Imaginary skew matrix units are Hermitian, including repeated indices. -/
theorem isHermitian_hermitianUnitIm (i j : n) : (hermitianUnitIm i j).IsHermitian := by
  unfold hermitianUnitIm Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub]
  simp only [conjTranspose_single, star_one, Complex.star_def, Complex.conj_I]
  rw [neg_smul, ← smul_neg, neg_sub]

/-- A plus/minus real quadratic probe extracts the symmetric entry sum. -/
theorem matrixQuadraticFormCLM_single_add_sub (A : Matrix n n ℂ) (i j : n) :
    matrixQuadraticFormCLM (Pi.single i 1 + Pi.single j 1) A -
      matrixQuadraticFormCLM (Pi.single i 1 - Pi.single j 1) A =
        2 * (A i j + A j i) := by
  simp only [matrixQuadraticFormCLM_apply, star_add, star_sub, Pi.star_single, star_one,
    Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, one_mul,
    mulVec_single_one, Matrix.col_apply]
  ring

/-- A plus/minus imaginary quadratic probe extracts the skew entry sum. -/
theorem matrixQuadraticFormCLM_single_add_sub_I (A : Matrix n n ℂ) (i j : n) :
    matrixQuadraticFormCLM (Pi.single i 1 + Complex.I • Pi.single j 1) A -
      matrixQuadraticFormCLM (Pi.single i 1 - Complex.I • Pi.single j 1) A =
        2 * Complex.I * (A i j - A j i) := by
  simp only [matrixQuadraticFormCLM_apply, star_add, star_sub, star_smul, Pi.star_single,
    star_one, Complex.star_def, Complex.conj_I, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_dotProduct, single_dotProduct, one_mul,
    mulVec_single_one, Matrix.col_apply, smul_eq_mul]
  ring

/-- The finite Hermitian matrix-unit family spans every complex matrix;
ordered pairs are used uniformly, with no chosen order on the indices. -/
theorem sum_hermitianUnit_eq (A : Matrix n n ℂ) :
    (∑ i, ∑ j, ((A i j + A j i) / 4) • hermitianUnitRe i j) +
      (∑ i, ∑ j, ((A i j - A j i) / (4 * Complex.I)) • hermitianUnitIm i j) = A := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [hermitianUnitRe, hermitianUnitIm, Matrix.single_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ite_and, mul_ite,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  field_simp
  ring

end Matrix

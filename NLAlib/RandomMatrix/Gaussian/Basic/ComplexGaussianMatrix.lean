import NLAlib.Probability.Gaussian.Basic.ComplexUnitary
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Native circular complex Gaussian matrices

The entries have independent standard real and imaginary coordinates. The
unit-variance convention is its deterministic scaling by `1/sqrt 2`. The
joint product law, rather than separate scalar marginals, is transported by
rectangular complex coisometries.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib

/-- An actual complex Gaussian matrix with independent `N(0,1)` real and
imaginary coordinates in every entry. -/
def circularComplexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℂ) :=
  (Measure.pi fun _ : m => circularComplexGaussianVector n).map Matrix.ofMeasurableEquiv

instance isProbabilityMeasure_circularComplexGaussianMatrix
    (m n : Type*) [Fintype m] [Fintype n] : IsProbabilityMeasure (circularComplexGaussianMatrix m n) := by
  unfold circularComplexGaussianMatrix
  exact Measure.isProbabilityMeasure_map Matrix.ofMeasurableEquiv.measurable.aemeasurable

/-- The unit-variance complex Gaussian matrix law: each entry is
`(g+i h)/sqrt 2` for independent standard real Gaussians. -/
def complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℂ) :=
  (circularComplexGaussianMatrix m n).map (fun G => (Real.sqrt 2)⁻¹ • G)

instance isProbabilityMeasure_complexGaussianMatrix
    (m n : Type*) [Fintype m] [Fintype n] : IsProbabilityMeasure (complexGaussianMatrix m n) := by
  unfold complexGaussianMatrix
  exact Measure.isProbabilityMeasure_map (by fun_prop)

variable {m n t p : Type*} [Fintype m] [Fintype n] [Fintype t] [Fintype p]

/-- Independent complex Gaussian rows carry the matrix product law. -/
theorem measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix :
    MeasurePreserving (Matrix.ofMeasurableEquiv : (m → n → ℂ) ≃ᵐ Matrix m n ℂ)
      (Measure.pi fun _ : m => circularComplexGaussianVector n)
      (circularComplexGaussianMatrix m n) :=
  ⟨Matrix.ofMeasurableEquiv.measurable, rfl⟩

/-- Integrals against the native complex matrix law reduce to the independent
complex row product law. -/
theorem integral_circularComplexGaussianMatrix_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Matrix m n ℂ → E) :
    ∫ G, F G ∂circularComplexGaussianMatrix m n =
      ∫ x, F (Matrix.of x) ∂Measure.pi (fun _ : m => circularComplexGaussianVector n) :=
  (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix.integral_comp' F).symm

/-- Integrability against the native complex matrix law reduces to the
independent complex row product law. -/
theorem integrable_circularComplexGaussianMatrix_iff
    {E : Type*} [NormedAddCommGroup E] {F : Matrix m n ℂ → E} :
    Integrable F (circularComplexGaussianMatrix m n) ↔
      Integrable (fun x => F (Matrix.of x)) (Measure.pi fun _ : m => circularComplexGaussianVector n) :=
  (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix.integrable_comp_emb
    Matrix.ofMeasurableEquiv.measurableEmbedding).symm

/-- Flattening gives exactly the native complex Gaussian vector law. -/
theorem circularComplexGaussianMatrix_map_uncurry :
    (circularComplexGaussianMatrix m n).map (fun G => fun ij : m × n => G ij.1 ij.2) =
      circularComplexGaussianVector (m × n) := by
  have he := Measure.infinitePi_map_curry (fun (_ : m) (_ : n) => circularComplexGaussian)
  simp only [Measure.infinitePi_eq_pi] at he
  have hm : Measurable (fun G : Matrix m n ℂ => fun ij : m × n => G ij.1 ij.2) :=
    measurable_pi_lambda _ fun ij => Matrix.measurable_entry ij.1 ij.2
  rw [circularComplexGaussianMatrix, ← he,
    Measure.map_map Matrix.ofMeasurableEquiv.measurable (MeasurableEquiv.curry m n ℂ).measurable,
    Measure.map_map hm (Matrix.ofMeasurableEquiv.measurable.comp (MeasurableEquiv.curry m n ℂ).measurable)]
  exact Measure.map_id

/-- Currying the native complex product vector gives the matrix law. -/
theorem hasLaw_curry_circularComplexGaussianVector :
    HasLaw (fun z : m × n → ℂ => Matrix.of fun i j => z (i,j))
      (circularComplexGaussianMatrix m n) (circularComplexGaussianVector (m × n)) := by
  refine ⟨(by fun_prop : Measurable (fun z : m × n → ℂ => Matrix.of fun i j => z (i,j))).aemeasurable, ?_⟩
  have he := Measure.infinitePi_map_curry (fun (_ : m) (_ : n) => circularComplexGaussian)
  simp only [Measure.infinitePi_eq_pi] at he
  rw [circularComplexGaussianMatrix, ← he,
    Measure.map_map Matrix.ofMeasurableEquiv.measurable (MeasurableEquiv.curry m n ℂ).measurable]
  rfl

/-- Left multiplication by a complex coisometry preserves the complete
independent complex matrix product law. -/
theorem hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows
    [DecidableEq m] [DecidableEq p] [DecidableEq t]
    (U : Matrix p m ℂ) (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun G : Matrix m t ℂ => U*G) (circularComplexGaussianMatrix p t)
      (circularComplexGaussianMatrix m t) := by
  have hK : HasOrthonormalCols (U ⊗ₖ (1 : Matrix t t ℂ))ᴴ := by
    change (U ⊗ₖ (1 : Matrix t t ℂ))ᴴᴴ * (U ⊗ₖ (1 : Matrix t t ℂ))ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      show U*Uᴴ=1 from by simpa only [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose] using hU,
      Matrix.one_kronecker_one]
  have hflat : HasLaw (fun G : Matrix m t ℂ => fun ij : m × t => G ij.1 ij.2)
      (circularComplexGaussianVector (m × t)) (circularComplexGaussianMatrix m t) :=
    ⟨(by fun_prop : Measurable _).aemeasurable, circularComplexGaussianMatrix_map_uncurry⟩
  have hG := (hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows
    (U ⊗ₖ (1 : Matrix t t ℂ)) hK).comp hflat
  have h := hasLaw_curry_circularComplexGaussianVector.comp hG
  apply h.congr
  apply Filter.Eventually.of_forall
  intro G
  ext i j
  simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

end NLAlib

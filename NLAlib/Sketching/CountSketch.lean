import NLAlib.Sketching.SubspaceEmbedding
import NLAlib.Concentration.RademacherQuadraticMoments
import Mathlib.Probability.Distributions.Uniform

/-!
# The actual CountSketch construction and its hollow Gram form

Each input column has its independently chosen hash row and sign. The law is
the product of the uniform hash-vector law and the actual Rademacher sign law.
The algebraic Gram error is expressed as a zero-diagonal sign quadratic form,
ready for the exact second-moment calculation.
Source: operator manuscript `sh:count-hollow`, `sh:count-second`, `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Matrix
namespace NLAlib

variable {ι ρ d : Type*} [Fintype ι] [Fintype ρ] [Fintype d]
variable [DecidableEq ι] [DecidableEq ρ] [DecidableEq d]

/-- A CountSketch has the chosen sign in its chosen hash row and zero
elsewhere. Source: manuscript `sh:count-hollow`; supports `sparse-ose`. -/
def countSketchMatrix (h : ι → ρ) (σ : ι → ℝ) : Matrix ρ ι ℝ :=
  Matrix.of fun r i => if h i = r then σ i else 0

omit [DecidableEq d] [Fintype d] [Fintype ι] [DecidableEq ι] in
/-- The Gram entry of a CountSketch is the sign product times the actual
hash-collision indicator. Source: manuscript `sh:count-hollow`;
supports `sparse-ose`. -/
theorem transpose_countSketchMatrix_mul_apply
    (h : ι → ρ) (σ : ι → ℝ) (i j : ι) :
    ((countSketchMatrix h σ)ᵀ * countSketchMatrix h σ) i j =
      if h i = h j then σ i * σ j else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, countSketchMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (h i)]
  · by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro r _ hri
    simp [Ne.symm hri]
  · simp

variable [MeasurableSpace ρ] [Nonempty ρ]

omit [DecidableEq ι] [DecidableEq ρ] [DecidableEq d] [Fintype d] in
/-- The actual CountSketch sampling law: independent uniform hash rows and
independent Rademacher signs, with the two families independent. Source:
manuscript `sh:count-second`; supports `sparse-ose`. -/
def countSketchLaw : Measure ((ι → ρ) × (ι → ℝ)) :=
  (Measure.pi fun _ : ι => (PMF.uniformOfFintype ρ).toMeasure).prod
    (Measure.pi fun _ : ι => rademacherMeasure)

omit [DecidableEq ι] [DecidableEq ρ] [DecidableEq d] [Fintype d] in
/-- The concrete CountSketch law is a probability measure. Source: product
of its normalized scalar laws; supports `sparse-ose`. -/
instance isProbabilityMeasure_countSketchLaw : IsProbabilityMeasure (countSketchLaw (ι := ι) (ρ := ρ)) := by
  unfold countSketchLaw
  infer_instance

omit [MeasurableSpace ρ] [Nonempty ρ] in
/-- The zero-diagonal coefficient matrix for an entry of the CountSketch
Gram error. Source: manuscript `sh:count-hollow`; supports `sparse-ose`. -/
def countSketchHollowCoefficient (h : ι → ρ) (U : Matrix ι d ℝ) (a b : d) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if i = j then 0 else if h i = h j then U i a * U j b else 0

omit [MeasurableSpace ρ] [Nonempty ρ] [Fintype ι] [Fintype ρ] [Fintype d] [DecidableEq d] in
/-- The coefficient matrix has zero diagonal by construction. Source:
manuscript `sh:count-hollow`; supports `sparse-ose`. -/
@[simp] theorem countSketchHollowCoefficient_diag
    (h : ι → ρ) (U : Matrix ι d ℝ) (a b : d) (i : ι) :
    countSketchHollowCoefficient h U a b i i = 0 := by
  simp [countSketchHollowCoefficient]

omit [MeasurableSpace ρ] [Nonempty ρ] [Fintype d] [DecidableEq d] in
/-- Unit-squared signs give the exact hollow sign quadratic form for every
entry of the embedded CountSketch Gram error. Source: manuscript
`sh:count-hollow`; supports `sparse-ose`. No random-data premise is added. -/
theorem mul_countSketchGram_sub_one_mul_apply_eq_quadForm
    (h : ι → ρ) (σ : ι → ℝ) (hσ : ∀ i, σ i ^ 2 = 1)
    (U : Matrix ι d ℝ) (a b : d) :
    (Uᵀ * ((countSketchMatrix h σ)ᵀ * countSketchMatrix h σ - 1) * U : Matrix d d ℝ) a b =
      quadForm (countSketchHollowCoefficient h U a b) σ := by
  have hgram (i j : ι) :
      (((countSketchMatrix h σ)ᵀ * countSketchMatrix h σ - 1) : Matrix ι ι ℝ) i j =
        if i = j then 0 else if h i = h j then σ i * σ j else 0 := by
    rw [Matrix.sub_apply, transpose_countSketchMatrix_mul_apply]
    by_cases hij : i = j
    · subst j
      simp only [if_true, Matrix.one_apply_eq, ← pow_two, hσ, sub_self]
    · simp only [hij, if_false, Matrix.one_apply_ne hij, sub_zero]
  rw [Matrix.mul_assoc, Matrix.mul_apply, quadForm_eq_sum]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, hgram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j <;> by_cases hh : h i = h j <;>
    simp only [hij, hh, if_true, if_false, countSketchHollowCoefficient, Matrix.of_apply,
      mul_zero, zero_mul]; ring

omit [MeasurableSpace ρ] [Nonempty ρ] [Fintype d] in
/-- An orthonormal frame removes the identity contribution from the embedded
Gram matrix. Source: manuscript `sh:count-hollow`; supports `sparse-ose`. -/
theorem countSketch_gram_error_eq
    (h : ι → ρ) (σ : ι → ℝ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1 =
      Uᵀ * ((countSketchMatrix h σ)ᵀ * countSketchMatrix h σ - 1) * U := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end NLAlib

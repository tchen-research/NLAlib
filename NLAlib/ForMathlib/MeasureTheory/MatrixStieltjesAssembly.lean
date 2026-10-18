import NLAlib.ForMathlib.MeasureTheory.PositiveMatrixMeasure
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.SignedStieltjes

/-!
# Positive matrix Stieltjes assembly from Hermitian coordinates

Finite signed coordinates in a Hermitian spanning family define a native
matrix vector measure. Positivity is proved by identifying every quadratic
signed projection with its actual positive scalar Stieltjes measure.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace MeasureTheory
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

omit [DecidableEq n] in
/-- Signed quadratic projections of a Hermitian coordinate combination
have exactly the corresponding matrix quadratic Stieltjes transform. -/
theorem stieltjesTransform_quadraticMeasureCombination
    (H : κ → Matrix n n ℂ) (hH : ∀ k, (H k).IsHermitian) (s : κ → SignedMeasure ℝ)
    (M : ℂ → Matrix n n ℂ)
    (hM : ∀ z : ℂ, 0 < z.im → M z = ∑ k, (s k).stieltjesTransform z • H k)
    (v : n → ℂ) {z : ℂ} (hz : 0 < z.im) :
    (quadraticMeasureCombination H s v).stieltjesTransform z = matrixQuadraticFormCLM v (M z) := by
  rw [quadraticMeasureCombination, SignedMeasure.stieltjesTransform_sum _ _ hz]
  simp only [SignedMeasure.stieltjesTransform_smul, Complex.real_smul]
  rw [hM z hz, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, smul_eq_mul]
  have hre : ((matrixRealQuadraticFormCLM v (H k) : ℝ) : ℂ) =
      matrixQuadraticFormCLM v (H k) := by
    apply Complex.ext
    · rfl
    · exact (hH k).im_star_dotProduct_mulVec_self v |>.symm
  rw [hre]
  ring

omit [DecidableEq n] in
/-- Positive scalar transforms force each signed quadratic coordinate
measure to be nonnegative on all measurable sets. -/
theorem quadraticMeasureCombination_nonneg_of_stieltjes
    (H : κ → Matrix n n ℂ) (hH : ∀ k, (H k).IsHermitian) (s : κ → SignedMeasure ℝ)
    (M : ℂ → Matrix n n ℂ)
    (hM : ∀ z : ℂ, 0 < z.im → M z = ∑ k, (s k).stieltjesTransform z • H k)
    (hscalar : ∀ v : n → ℂ, ∃ μ : FiniteMeasure ℝ, ∀ z : ℂ, 0 < z.im →
      matrixQuadraticFormCLM v (M z) = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ)) :
    ∀ v : n → ℂ, ∀ E : Set ℝ, MeasurableSet E →
      0 ≤ quadraticMeasureCombination H s v E := by
  intro v E hE
  obtain ⟨μ, hμ⟩ := hscalar v
  have he : quadraticMeasureCombination H s v = (μ : Measure ℝ).toSignedMeasure := by
    apply SignedMeasure.eq_of_stieltjesTransform_eq
    intro z hz
    rw [stieltjesTransform_quadraticMeasureCombination H hH s M hM v hz,
      SignedMeasure.stieltjesTransform_toSignedMeasure]
    exact hμ z hz
  rw [he, Measure.toSignedMeasure_apply_measurable hE]
  exact measureReal_nonneg

/-- Actual positive scalar quadratic representations assemble to a native
positive matrix measure whenever finite Hermitian coordinates reproduce
the matrix transform. The coordinates are instantiated by polarization
of the scalar measures in the analytic capstone. -/
theorem exists_positiveMatrixMeasure_of_stieltjesCombination
    (H : κ → Matrix n n ℂ) (hH : ∀ k, (H k).IsHermitian) (s : κ → SignedMeasure ℝ)
    (M : ℂ → Matrix n n ℂ)
    (hM : ∀ z : ℂ, 0 < z.im → M z = ∑ k, (s k).stieltjesTransform z • H k)
    (hscalar : ∀ v : n → ℂ, ∃ μ : FiniteMeasure ℝ, ∀ z : ℂ, 0 < z.im →
      matrixQuadraticFormCLM v (M z) = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ)) :
    ∃ μ : PositiveMatrixMeasure ℝ n,
      μ.toVectorMeasure = matrixMeasureCombination H s ∧
      ∀ v : n → ℂ, ∀ z : ℂ, 0 < z.im →
        (μ.quadraticForm v).stieltjesTransform z = matrixQuadraticFormCLM v (M z) := by
  let μ := positiveMatrixMeasureOfCombination H hH s
    (quadraticMeasureCombination_nonneg_of_stieltjes H hH s M hM hscalar)
  refine ⟨μ, rfl, ?_⟩
  intro v z hz
  have he : μ.quadraticForm v = quadraticMeasureCombination H s v := by
    apply VectorMeasure.ext
    intro E _
    exact (quadraticMeasureCombination_apply H s v E).symm
  rw [he]
  exact stieltjesTransform_quadraticMeasureCombination H hH s M hM v hz

end MeasureTheory

import NLAlib.ForMathlib.MeasureTheory.MatrixStieltjesAssembly
import NLAlib.ForMathlib.Analysis.Matrix.HermitianSpanning

/-!
# Polarization constructs a positive matrix Stieltjes measure

Four actual positive scalar quadratic measures provide signed coordinates
in a finite Hermitian spanning family. Signed uniqueness proves positivity
on all measurable sets; it is not an additional consistency hypothesis.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The uniformly indexed finite Hermitian spanning family. -/
def polarizationHermitianFamily : ((n × n) ⊕ (n × n)) → Matrix n n ℂ :=
  Sum.elim (fun p => hermitianUnitRe p.1 p.2) (fun p => hermitianUnitIm p.1 p.2)

omit [Fintype n] in
/-- Each polarization coordinate is Hermitian. -/
theorem isHermitian_polarizationHermitianFamily (k : (n × n) ⊕ (n × n)) :
    (polarizationHermitianFamily k).IsHermitian := by
  cases k with
  | inl p => exact isHermitian_hermitianUnitRe p.1 p.2
  | inr p => exact isHermitian_hermitianUnitIm p.1 p.2

/-- Real signed coordinates obtained by polarizing actual positive
quadratic measures. The eighth factor accounts for the ordered-pair
Hermitian spanning family, including diagonal pairs. -/
def polarizationSignedCoordinates (μ : (n → ℂ) → FiniteMeasure ℝ) :
    ((n × n) ⊕ (n × n)) → SignedMeasure ℝ :=
  Sum.elim
    (fun p => (1 / 8 : ℝ) •
      ((μ (Pi.single p.1 1 + Pi.single p.2 1) : Measure ℝ).toSignedMeasure -
        (μ (Pi.single p.1 1 - Pi.single p.2 1) : Measure ℝ).toSignedMeasure))
    (fun p => (-1 / 8 : ℝ) •
      ((μ (Pi.single p.1 1 + Complex.I • Pi.single p.2 1) : Measure ℝ).toSignedMeasure -
        (μ (Pi.single p.1 1 - Complex.I • Pi.single p.2 1) : Measure ℝ).toSignedMeasure))

/-- Polarized signed coordinates reproduce each matrix transform entry. -/
theorem sum_stieltjesTransform_polarizationSignedCoordinates
    (M : ℂ → Matrix n n ℂ) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0 < z.im →
      matrixQuadraticFormCLM v (M z) = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ v : Measure ℝ))
    {z : ℂ} (hz : 0 < z.im) :
    M z = ∑ k, (polarizationSignedCoordinates μ k).stieltjesTransform z •
      polarizationHermitianFamily k := by
  rw [Fintype.sum_sum_type]
  simp only [polarizationSignedCoordinates, polarizationHermitianFamily, Sum.elim_inl,
    Sum.elim_inr, SignedMeasure.stieltjesTransform_smul,
    SignedMeasure.stieltjesTransform_sub _ _ hz, SignedMeasure.stieltjesTransform_toSignedMeasure,
    Complex.real_smul, ← hμ _ z hz]
  simp_rw [matrixQuadraticFormCLM_single_add_sub, matrixQuadraticFormCLM_single_add_sub_I]
  have hr (i j : n) :
      ((1 / 8 : ℝ) : ℂ) * (2 * ((M z) i j + (M z) j i)) =
        ((M z) i j + (M z) j i) / 4 := by push_cast; ring
  have hi (i j : n) :
      ((-1 / 8 : ℝ) : ℂ) * (2 * Complex.I * ((M z) i j - (M z) j i)) =
        ((M z) i j - (M z) j i) / (4 * Complex.I) := by
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  simp_rw [hr, hi, Fintype.sum_prod_type]
  exact (sum_hermitianUnit_eq (M z)).symm

/-- Actual positive scalar measures for every quadratic probe assemble
to one native positive matrix-valued measure. Each quadratic signed
projection is exactly its original positive scalar measure. -/
theorem exists_positiveMatrixMeasure_of_quadratic_stieltjes
    (M : ℂ → Matrix n n ℂ) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0 < z.im →
      matrixQuadraticFormCLM v (M z) = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ v : Measure ℝ)) :
    ∃ P : PositiveMatrixMeasure ℝ n, ∀ v : n → ℂ,
      P.quadraticForm v = (μ v : Measure ℝ).toSignedMeasure := by
  obtain ⟨P, _hP, hrep⟩ := exists_positiveMatrixMeasure_of_stieltjesCombination
    polarizationHermitianFamily isHermitian_polarizationHermitianFamily
    (polarizationSignedCoordinates μ) M
    (fun _ hz => sum_stieltjesTransform_polarizationSignedCoordinates M μ hμ hz)
    (fun v => ⟨μ v, hμ v⟩)
  refine ⟨P, ?_⟩
  intro v
  apply SignedMeasure.eq_of_stieltjesTransform_eq
  intro z hz
  rw [hrep v z hz, SignedMeasure.stieltjesTransform_toSignedMeasure]
  exact hμ v z hz

end MeasureTheory

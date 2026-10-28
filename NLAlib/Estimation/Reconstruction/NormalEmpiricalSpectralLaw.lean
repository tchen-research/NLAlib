import NLAlib.Estimation.Reconstruction.NormalSpectralCoordinates

/-!
# Empirical spectral laws of normal matrices

Every eigenvalue is counted with multiplicity. Integration is normalized native
functional-calculus trace, proving independence from the chosen eigenbasis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped NNReal ENNReal
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The uniform atomic law of a finite complex eigenvalue list. -/
def uniformComplexSpectralLaw (d : n → ℂ) : Measure ℂ :=
  (Fintype.card n : ℝ≥0)⁻¹ • ∑ i, Measure.dirac (d i)

instance uniformComplexSpectralLaw_isFiniteMeasure (d : n → ℂ) :
    IsFiniteMeasure (uniformComplexSpectralLaw d) := by
  unfold uniformComplexSpectralLaw
  infer_instance

omit [DecidableEq n] in
/-- Arbitrary tests are integrable on a finite spectrum. -/
theorem integrable_uniformComplexSpectralLaw (d : n → ℂ) (f : ℂ → ℂ) :
    Integrable f (uniformComplexSpectralLaw d) := by
  apply Integrable.smul_measure_nnreal
  exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by simp))

omit [DecidableEq n] in
/-- The actual uniform finite-law integral is the arithmetic mean. -/
theorem integral_uniformComplexSpectralLaw (d : n → ℂ) (f : ℂ → ℂ) :
    ∫ z, f z ∂uniformComplexSpectralLaw d = (∑ i, f (d i))/(Fintype.card n : ℂ) := by
  rw [uniformComplexSpectralLaw, integral_smul_nnreal_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_natCast,
    RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

instance uniformComplexSpectralLaw_isProbabilityMeasure [Nonempty n] (d : n → ℂ) :
    IsProbabilityMeasure (uniformComplexSpectralLaw d) := by
  constructor
  simp only [uniformComplexSpectralLaw, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [ENNReal.smul_def]
  simp only [smul_eq_mul]
  rw [ENNReal.coe_inv (show (Fintype.card n : ℝ≥0) ≠ 0 by
    exact_mod_cast Fintype.card_ne_zero (α := n)), ENNReal.coe_natCast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := n)) (by simp)

open scoped Matrix.Norms.L2Operator in
private theorem integral_uniformComplexSpectralLaw_eq_trace_cfc
    {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hU : A = (U : Matrix n n ℂ)*Matrix.diagonal d*(U : Matrix n n ℂ)ᴴ)
    (f : ℂ → ℂ) :
    ∫ z, f z ∂uniformComplexSpectralLaw d = (cfc f A).trace/(Fintype.card n : ℂ) := by
  have hn : IsStarNormal (Matrix.diagonal d) := by
    constructor
    change (Matrix.diagonal d)ᴴ * Matrix.diagonal d = Matrix.diagonal d * (Matrix.diagonal d)ᴴ
    simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [integral_uniformComplexSpectralLaw,hU,cfc_complex_unitary_conj U f _ hn,
    cfc_diagonal_complex, Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

/-- The native empirical law of a normal matrix. -/
def normalEmpiricalSpectralLaw {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) : Measure ℂ :=
  uniformComplexSpectralLaw (exists_unitary_diagonalization_of_normal hA).choose_spec.choose

instance normalEmpiricalSpectralLaw_isFiniteMeasure {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) : IsFiniteMeasure (normalEmpiricalSpectralLaw hA) := by
  unfold normalEmpiricalSpectralLaw
  infer_instance

instance normalEmpiricalSpectralLaw_isProbabilityMeasure [Nonempty n] {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) : IsProbabilityMeasure (normalEmpiricalSpectralLaw hA) := by
  unfold normalEmpiricalSpectralLaw
  infer_instance

open scoped Matrix.Norms.L2Operator in
/-- Empirical spectral integration is normalized native functional-calculus trace. -/
theorem integral_normalEmpiricalSpectralLaw_eq_trace_cfc {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) (f : ℂ → ℂ) :
    ∫ z, f z ∂normalEmpiricalSpectralLaw hA = (cfc f A).trace/(Fintype.card n : ℂ) :=
  integral_uniformComplexSpectralLaw_eq_trace_cfc _ _
    (exists_unitary_diagonalization_of_normal hA).choose_spec.choose_spec f

open scoped Matrix.Norms.L2Operator in
/-- Every unitary diagonalization gives the same empirical law, with repeated
spectra retained with their multiplicities. -/
theorem normalEmpiricalSpectralLaw_eq_uniformComplexSpectralLaw {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hU : A = (U : Matrix n n ℂ)*Matrix.diagonal d*(U : Matrix n n ℂ)ᴴ) :
    normalEmpiricalSpectralLaw hA = uniformComplexSpectralLaw d := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have he := (integral_normalEmpiricalSpectralLaw_eq_trace_cfc hA (fun z => (f z : ℂ))).trans
    (integral_uniformComplexSpectralLaw_eq_trace_cfc U d hU (fun z => (f z : ℂ))).symm
  simp only [integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

/-- The empirical normal law in isometric Euclidean real/imaginary coordinates. -/
def normalEmpiricalCoordinateSpectralLaw {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  (normalEmpiricalSpectralLaw hA).map Complex.orthonormalBasisOneI.repr

instance normalEmpiricalCoordinateSpectralLaw_isProbabilityMeasure [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) :
    IsProbabilityMeasure (normalEmpiricalCoordinateSpectralLaw hA) :=
  Measure.isProbabilityMeasure_map Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable

open scoped Matrix.Norms.L2Operator in
/-- Every empirical eigenvalue lies in the native spectral-norm disk. -/
theorem ae_norm_le_normalEmpiricalSpectralLaw {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) :
    ∀ᵐ z ∂normalEmpiricalSpectralLaw hA, ‖z‖ ≤ specNorm A := by
  obtain ⟨U,d,hU⟩ := exists_unitary_diagonalization_of_normal hA
  rw [normalEmpiricalSpectralLaw_eq_uniformComplexSpectralLaw hA U d hU,
    uniformComplexSpectralLaw]
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  let : Nonempty n := ⟨i⟩
  apply (ae_dirac_iff (measurableSet_le (by fun_prop) measurable_const)).mpr
  have hs : spectrum ℂ A = Set.range d := by
    rw [hU]
    simpa only [← Matrix.star_eq_conjTranspose,Unitary.coe_star,spectrum_diagonal] using
      (Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal d) (U := U))
  have hm : d i ∈ spectrum ℂ A := hs.symm ▸ Set.mem_range_self i
  simpa only [← specNorm_eq_norm] using spectrum.norm_le_norm_of_mem hm

/-- Contractive normal empirical laws lie in the exact Euclidean Chebyshev cube. -/
theorem ae_mem_chebyshevCube_normalEmpiricalCoordinateSpectralLaw
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) (hbound : specNorm A ≤ 1) :
    ∀ᵐ x ∂normalEmpiricalCoordinateSpectralLaw hA, x ∈ chebyshevCube (Fin 2) := by
  rw [normalEmpiricalCoordinateSpectralLaw,ae_map_iff
    Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable]
  filter_upwards [ae_norm_le_normalEmpiricalSpectralLaw hA] with z hz
  have hz1 := hz.trans hbound
  intro i
  fin_cases i
  · exact abs_le.mp ((Complex.abs_re_le_norm z).trans hz1)
  · exact abs_le.mp ((Complex.abs_im_le_norm z).trans hz1)
  · exact isCompact_chebyshevCube.isClosed.measurableSet

/-- Isometric coordinate transport is exactly reversible for the empirical law. -/
theorem map_normalEmpiricalCoordinateSpectralLaw_symm {A : Matrix n n ℂ}
    (hA : A*Aᴴ = Aᴴ*A) :
    (normalEmpiricalCoordinateSpectralLaw hA).map Complex.orthonormalBasisOneI.repr.symm =
      normalEmpiricalSpectralLaw hA := by
  rw [normalEmpiricalCoordinateSpectralLaw,Measure.map_map
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable
    Complex.orthonormalBasisOneI.repr.continuous.measurable]
  simp only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply]
  exact Measure.map_id

end NLAlib

import NLAlib.Estimation.Reconstruction.NormalSpectralLaw
import NLAlib.Polynomial.FunctionApproximation.ChebyshevCube

/-!
# Isometric real coordinates for complex spectral laws

Mathlib's orthonormal basis `(1,i)` identifies the complex plane with real
Euclidean two-space, so the transport has no distortion of distance.
-/

noncomputable section
open scoped Matrix
open MeasureTheory
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral law in isometric real/imaginary Euclidean coordinates. -/
def normalCoordinateSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (normalSpectralLaw hA b).map Complex.orthonormalBasisOneI.repr

/-- The coordinate law is an actual probability measure for a unit start. -/
theorem isProbabilityMeasure_normalCoordinateSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    IsProbabilityMeasure (normalCoordinateSpectralLaw hA b) := by
  have := isProbabilityMeasure_normalSpectralLaw hA b hb
  exact Measure.isProbabilityMeasure_map Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable

/-- Isometric coordinate transport is exactly reversible on the native law. -/
theorem map_normalCoordinateSpectralLaw_symm {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) :
    (normalCoordinateSpectralLaw hA b).map Complex.orthonormalBasisOneI.repr.symm =
      normalSpectralLaw hA b := by
  rw [normalCoordinateSpectralLaw, Measure.map_map
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable
    Complex.orthonormalBasisOneI.repr.continuous.measurable]
  simp only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply]
  change Measure.map id (normalSpectralLaw hA b) = normalSpectralLaw hA b
  exact Measure.map_id

open scoped Matrix.Norms.L2Operator in
/-- Every normal spectral atom lies in the disk controlled by the spectral norm. -/
theorem ae_norm_le_normalSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) :
    ∀ᵐ z ∂normalSpectralLaw hA b, ‖z‖ ≤ specNorm A := by
  obtain ⟨U,d,hU⟩ := exists_unitary_diagonalization_of_normal hA
  rw [normalSpectralLaw_eq_diagonalSpectralLaw hA U d hU b, diagonalSpectralLaw,
    ae_finsetSum_measure_iff]
  intro i _
  let : Nonempty n := ⟨i⟩
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff (measurableSet_le (by fun_prop) measurable_const)).mpr
  have hs : spectrum ℂ A = Set.range d := by
    rw [hU]
    simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal] using
      (Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal d) (U := U))
  have hm : d i ∈ spectrum ℂ A := hs.symm ▸ Set.mem_range_self i
  simpa only [← specNorm_eq_norm] using spectrum.norm_le_norm_of_mem hm

/-- Contractive normal spectral laws have their coordinate law in the exact
Euclidean Chebyshev square used by the tensor reconstruction.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem ae_mem_chebyshevCube_normalCoordinateSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (hbound : specNorm A ≤ 1) :
    ∀ᵐ x ∂normalCoordinateSpectralLaw hA b, x ∈ chebyshevCube (Fin 2) := by
  rw [normalCoordinateSpectralLaw, ae_map_iff
    Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable]
  filter_upwards [ae_norm_le_normalSpectralLaw hA b] with z hz
  have hz1 := hz.trans hbound
  intro i
  fin_cases i
  · exact abs_le.mp ((Complex.abs_re_le_norm z).trans hz1)
  · exact abs_le.mp ((Complex.abs_im_le_norm z).trans hz1)
  · exact isCompact_chebyshevCube.isClosed.measurableSet

end NLAlib

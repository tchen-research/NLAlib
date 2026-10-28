import NLAlib.Matrix.Spectral.NormalSpectral
import NLAlib.Matrix.Functions.ComplexCalculus
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Vector-weighted spectral laws of normal matrices

A unitary eigenbasis gives the finite atomic law with squared spectral-coordinate
weights. Integrals are native functional-calculus quadratic forms, which makes
the law independent of the basis, including repeated eigenvalues.
Source: the normal spectral theorem; MMSUW 2026, Section 2.1.
-/

noncomputable section
open scoped Matrix NNReal ENNReal
open MeasureTheory
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The atomic spectral law written in a specified unitary eigenbasis. Its mass
is the squared norm of `b`; in particular it is a probability law for unit `b`. -/
def diagonalSpectralLaw (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ) (b : n → ℂ) : Measure ℂ :=
  ∑ i, (‖((U : Matrix n n ℂ)ᴴ *ᵥ b) i‖₊ ^ 2) • Measure.dirac (d i)

instance diagonalSpectralLaw_isFiniteMeasure (U : Matrix.unitaryGroup n ℂ)
    (d : n → ℂ) (b : n → ℂ) : IsFiniteMeasure (diagonalSpectralLaw U d b) := by
  unfold diagonalSpectralLaw
  infer_instance

/-- Every scalar test function is integrable against the finite spectral law. -/
theorem integrable_diagonalSpectralLaw (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (b : n → ℂ) (f : ℂ → ℂ) : Integrable f (diagonalSpectralLaw U d b) := by
  unfold diagonalSpectralLaw
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply Integrable.smul_measure_nnreal
  exact integrable_dirac (by simp)

/-- The actual spectral-law integral is the finite coordinate-weighted sum. -/
theorem integral_diagonalSpectralLaw (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (b : n → ℂ) (f : ℂ → ℂ) :
    ∫ z, f z ∂diagonalSpectralLaw U d b =
      ∑ i, (‖((U : Matrix n n ℂ)ᴴ *ᵥ b) i‖ ^ 2 : ℝ) • f (d i) := by
  unfold diagonalSpectralLaw
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, NNReal.coe_pow,
    coe_nnnorm]

private theorem quadForm_diagonal_eq_sum (d : n → ℂ) (c : n → ℂ) :
    quadForm (Matrix.diagonal d) c = ∑ i, (‖c i‖ ^ 2 : ℝ) • d i := by
  simp only [quadForm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply,
    RCLike.real_smul_eq_coe_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    star (c i) * (d i * c i) = d i * (c i * star (c i)) := by ring
    _ = _ := by rw [Complex.star_def, Complex.mul_conj]; simp [Complex.normSq_eq_norm_sq, mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- Spectral-law integrals agree with the quadratic form of native complex
functional calculus, for every test function on the finite spectrum.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem integral_diagonalSpectralLaw_eq_quadForm_cfc
    {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hA : A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ)
    (b : n → ℂ) (f : ℂ → ℂ) :
    ∫ z, f z ∂diagonalSpectralLaw U d b = quadForm (cfc f A) b := by
  rw [integral_diagonalSpectralLaw, hA, cfc_complex_unitary_conj,
    cfc_diagonal_complex]
  · simpa only [Matrix.conjTranspose_conjTranspose, quadForm_diagonal_eq_sum] using
      (quadForm_conjTranspose_mul_mul (Matrix.diagonal (fun i => f (d i)))
        (U : Matrix n n ℂ)ᴴ b).symm
  · constructor
    change (Matrix.diagonal d)ᴴ * Matrix.diagonal d =
      Matrix.diagonal d * (Matrix.diagonal d)ᴴ
    simp only [Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

/-- Unitary coordinates preserve the squared norm appearing in the total mass. -/
theorem sum_norm_sq_unitary_coordinates (U : Matrix.unitaryGroup n ℂ) (b : n → ℂ) :
    ∑ i, ‖((U : Matrix n n ℂ)ᴴ *ᵥ b) i‖ ^ 2 = ‖WithLp.toLp 2 b‖ ^ 2 := by
  have h := quadForm_conjTranspose_mul_mul (1 : Matrix n n ℂ) (U : Matrix n n ℂ)ᴴ b
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_one, hUU] at h
  have hh := congrArg Complex.re h
  simp only [quadForm, Matrix.one_mulVec] at hh
  change RCLike.re (star b ⬝ᵥ b) =
    RCLike.re (star ((U : Matrix n n ℂ)ᴴ *ᵥ b) ⬝ᵥ ((U : Matrix n n ℂ)ᴴ *ᵥ b)) at hh
  rw [← norm_toLp_sq_eq_re_star_dotProduct, ← norm_toLp_sq_eq_re_star_dotProduct] at hh
  rw [hh]
  exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 ((U : Matrix n n ℂ)ᴴ *ᵥ b))).symm

/-- Unit starting vectors give an actual probability law. -/
theorem isProbabilityMeasure_diagonalSpectralLaw (U : Matrix.unitaryGroup n ℂ)
    (d : n → ℂ) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    IsProbabilityMeasure (diagonalSpectralLaw U d b) := by
  constructor
  simp only [diagonalSpectralLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), ENNReal.smul_def,
    smul_eq_mul, mul_one]
  have hsum : (∑ i, ‖((U : Matrix n n ℂ)ᴴ *ᵥ b) i‖₊ ^ 2 : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm, NNReal.coe_one,
      sum_norm_sq_unitary_coordinates, hb, one_pow]
  exact_mod_cast hsum

open scoped Matrix.Norms.L2Operator in
/-- Different unitary eigenbases of the same normal matrix give the same actual
measure, including arbitrary rotations inside repeated eigenspaces.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem diagonalSpectralLaw_eq_of_diagonalizations {A : Matrix n n ℂ}
    (U V : Matrix.unitaryGroup n ℂ) (d e : n → ℂ)
    (hU : A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ)
    (hV : A = (V : Matrix n n ℂ) * Matrix.diagonal e * (V : Matrix n n ℂ)ᴴ)
    (b : n → ℂ) : diagonalSpectralLaw U d b = diagonalSpectralLaw V e b := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have h := (integral_diagonalSpectralLaw_eq_quadForm_cfc U d hU b (fun z => (f z : ℂ))).trans
    (integral_diagonalSpectralLaw_eq_quadForm_cfc V e hV b (fun z => (f z : ℂ))).symm
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- The native vector-weighted law of a normal matrix. A chosen diagonalization
defines it; the preceding theorem proves independence of that choice. -/
def normalSpectralLaw {A : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) : Measure ℂ :=
  let U := (exists_unitary_diagonalization_of_normal hA).choose
  let d := (exists_unitary_diagonalization_of_normal hA).choose_spec.choose
  diagonalSpectralLaw U d b

/-- The canonical law equals the source formula in every unitary eigenbasis. -/
theorem normalSpectralLaw_eq_diagonalSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hU : A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ) (b : n → ℂ) :
    normalSpectralLaw hA b = diagonalSpectralLaw U d b := by
  exact diagonalSpectralLaw_eq_of_diagonalizations _ _ _ _
    (exists_unitary_diagonalization_of_normal hA).choose_spec.choose_spec hU b

instance normalSpectralLaw_isFiniteMeasure {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) : IsFiniteMeasure (normalSpectralLaw hA b) := by
  unfold normalSpectralLaw
  infer_instance

/-- The eigenbasis-independent law is a probability law for every unit start.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem isProbabilityMeasure_normalSpectralLaw {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    IsProbabilityMeasure (normalSpectralLaw hA b) := by
  unfold normalSpectralLaw
  exact isProbabilityMeasure_diagonalSpectralLaw _ _ b hb

open scoped Matrix.Norms.L2Operator in
/-- Canonical spectral-law integration is the native functional-calculus
quadratic form for every function on the finite normal spectrum. -/
theorem integral_normalSpectralLaw_eq_quadForm_cfc {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (b : n → ℂ) (f : ℂ → ℂ) :
    ∫ z, f z ∂normalSpectralLaw hA b = quadForm (cfc f A) b := by
  exact integral_diagonalSpectralLaw_eq_quadForm_cfc _ _
    (exists_unitary_diagonalization_of_normal hA).choose_spec.choose_spec b f

end NLAlib

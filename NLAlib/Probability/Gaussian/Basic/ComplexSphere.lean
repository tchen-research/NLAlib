import NLAlib.Probability.Gaussian.Basic.ComplexUnitary
import NLAlib.Matrix.Norms.Core

/-!
# Normalized complex Gaussian vectors

Normalizing the actual circular Gaussian product gives the complex-sphere law.
The zero input is mapped to zero; it is a null event in positive dimension.
The law is supported on unit vectors and is invariant under every unitary.
The variance-one versus variance-two Gaussian convention has no effect on this
normalization. Source: the Gaussian construction of uniform sphere measure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- Radial normalization of a complex vector, with value zero at zero. -/
def normalizeComplexVector (z : n → ℂ) : n → ℂ := ‖WithLp.toLp 2 z‖⁻¹ • z

/-- Radial normalization is measurable, including its zero-input convention. -/
@[fun_prop] theorem measurable_normalizeComplexVector :
    Measurable (normalizeComplexVector : (n → ℂ) → n → ℂ) := by
  unfold normalizeComplexVector
  fun_prop

/-- The complex unit-sphere law, constructed from independent real/imaginary
standard Gaussian coordinates by radial normalization. -/
def complexSphereVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  (circularComplexGaussianVector n).map normalizeComplexVector

instance isProbabilityMeasure_complexSphereVector :
    IsProbabilityMeasure (complexSphereVector n) := by
  unfold complexSphereVector
  exact Measure.isProbabilityMeasure_map measurable_normalizeComplexVector.aemeasurable

/-- The actual Gaussian normalization has the sphere law by definition. -/
theorem hasLaw_normalizeComplexVector_circularComplexGaussianVector :
    HasLaw (normalizeComplexVector : (n → ℂ) → n → ℂ)
      (complexSphereVector n) (circularComplexGaussianVector n) :=
  ⟨measurable_normalizeComplexVector.aemeasurable, rfl⟩

/-- A nonzero input normalizes to a unit vector. -/
theorem norm_normalizeComplexVector {z : n → ℂ} (hz : z ≠ 0) :
    ‖WithLp.toLp 2 (normalizeComplexVector z)‖ = 1 := by
  have hn : ‖WithLp.toLp 2 z‖ ≠ 0 := by
    intro he
    exact hz ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp he))
  change ‖(‖WithLp.toLp 2 z‖⁻¹ : ℝ) • WithLp.toLp 2 z‖ = 1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

/-- In positive dimension a Gaussian vector is almost surely nonzero, already
because a single real coordinate has a nonatomic Gaussian law. -/
theorem ae_ne_zero_circularComplexGaussianVector [Nonempty n] :
    ∀ᵐ z ∂circularComplexGaussianVector n, z ≠ 0 := by
  let i : n := Classical.arbitrary n
  have hl := (hasLaw_eval_gaussianVector (Sum.inl i)).comp
    (hasLaw_realifyVector_circularComplexGaussianVector (n := n))
  have hz : (circularComplexGaussianVector n) {z | (z i).re = 0} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
    have he := hl.measure_eq (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)
    change (circularComplexGaussianVector n) {z | (z i).re = 0} =
      (gaussianReal 0 1) {0} at he
    exact he.trans (measure_singleton 0)
  rw [ae_iff]
  apply measure_mono_null (t := {z : n → ℂ | (z i).re = 0}) _ hz
  intro z h
  change ¬ z ≠ 0 at h
  have he : z = 0 := not_not.mp h
  simp [he]

/-- The complex-sphere law is supported on actual unit vectors. -/
theorem ae_norm_eq_one_complexSphereVector [Nonempty n] :
    ∀ᵐ b ∂complexSphereVector n, ‖WithLp.toLp 2 b‖ = 1 := by
  unfold complexSphereVector
  apply (ae_map_iff measurable_normalizeComplexVector.aemeasurable
    (p := fun b : n → ℂ => ‖WithLp.toLp 2 b‖ = 1) (by
      convert (by fun_prop : Measurable (fun b : n → ℂ => ‖WithLp.toLp 2 b‖))
        (measurableSet_singleton 1) using 1
      ext b
      simp)).mpr
  filter_upwards [ae_ne_zero_circularComplexGaussianVector (n := n)] with z hz
  exact norm_normalizeComplexVector hz

variable [DecidableEq n]

/-- Unitary changes of coordinates preserve the Euclidean normalization. -/
theorem normalizeComplexVector_mulVec {U : Matrix n n ℂ} (hU : HasOrthonormalCols U)
    (z : n → ℂ) :
    normalizeComplexVector (U *ᵥ z) = U *ᵥ normalizeComplexVector z := by
  have hn : ‖WithLp.toLp 2 (U *ᵥ z)‖ = ‖WithLp.toLp 2 z‖ :=
    hU.toLinearIsometry.norm_map (WithLp.toLp 2 z)
  rw [normalizeComplexVector, hn, normalizeComplexVector, Matrix.mulVec_smul]

/-- Every unitary preserves the actual normalized Gaussian sphere law. -/
theorem hasLaw_mulVec_complexSphereVector_unitary (U : Matrix n n ℂ)
    (hU : HasOrthonormalCols U) :
    HasLaw (fun b => U *ᵥ b) (complexSphereVector n) (complexSphereVector n) := by
  have hg := hasLaw_mulVec_circularComplexGaussianVector_unitary U hU
  have hs := (hasLaw_normalizeComplexVector_circularComplexGaussianVector (n := n)).comp hg
  refine ⟨(by fun_prop : Measurable (fun b : n → ℂ => U *ᵥ b)).aemeasurable, ?_⟩
  rw [complexSphereVector, Measure.map_map (by fun_prop) measurable_normalizeComplexVector]
  have hf : (fun b : n → ℂ => U *ᵥ b) ∘ normalizeComplexVector =
      normalizeComplexVector ∘ (fun z => U *ᵥ z) := by
    funext z
    exact (normalizeComplexVector_mulVec hU z).symm
  rw [hf]
  exact hs.map_eq

end NLAlib

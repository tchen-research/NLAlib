import NLAlib.RandomMatrix.Haar.UnitaryFrameMeasure
import NLAlib.Solvers.LeastSquares.Measurability
import Mathlib.Probability.HasLaw

/-!
# Actual ambient-matrix Haar laws and arbitrary sample-space transport

The native compact-Haar frame is embedded into the ambient matrix space.
Its adjoint is the actual sketch. Native integrability and expectation formulas
transport to any random matrix with exactly this law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib

/-- The actual ambient matrix law of an orthonormal-column Haar frame. -/
def unitaryHaarFrameMatrixLaw (K : Type*) [RCLike K] (n ell : ℕ) (helln : ell≤n) :
    Measure (Matrix (Fin n) (Fin ell) K) :=
  (unitaryHaarFrameLaw K n ell helln).map Subtype.val

instance unitaryHaarFrameMatrixLaw_isProbabilityMeasure (K : Type*) [RCLike K]
    (n ell : ℕ) (helln : ell≤n) : IsProbabilityMeasure (unitaryHaarFrameMatrixLaw K n ell helln) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- The actual sketch law is the adjoint of the ambient orthonormal-column law. -/
def unitaryHaarAdjointSketchLaw (K : Type*) [RCLike K] (n ell : ℕ) (helln : ell≤n) :
    Measure (Matrix (Fin ell) (Fin n) K) :=
  (unitaryHaarFrameMatrixLaw K n ell helln).map Matrix.conjTranspose

instance unitaryHaarAdjointSketchLaw_isProbabilityMeasure (K : Type*) [RCLike K]
    (n ell : ℕ) (helln : ell≤n) : IsProbabilityMeasure (unitaryHaarAdjointSketchLaw K n ell helln) :=
  Measure.isProbabilityMeasure_map Matrix.measurable_conjTranspose.aemeasurable

/-- The frame-to-matrix embedding has exactly the stated native ambient law. -/
theorem hasLaw_val_unitaryHaarFrameLaw (K : Type*) [RCLike K] {n ell : ℕ} (helln : ell≤n) :
    HasLaw (Subtype.val : UnitaryStiefel K n ell → Matrix (Fin n) (Fin ell) K)
      (unitaryHaarFrameMatrixLaw K n ell helln) (unitaryHaarFrameLaw K n ell helln) :=
  ⟨measurable_subtype_coe.aemeasurable,rfl⟩

/-- Any random matrix with the native frame-matrix law has the native adjoint
sketch law after taking its Hermitian adjoint. -/
theorem _root_.ProbabilityTheory.HasLaw.conjTranspose_unitaryHaarFrameMatrixLaw
    {K Ω : Type*} [RCLike K] [MeasurableSpace Ω] {μ : Measure Ω} {n ell : ℕ}
    {Z : Ω → Matrix (Fin n) (Fin ell) K} {helln : ell≤n}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw K n ell helln) μ) :
    HasLaw (fun ω => (Z ω)ᴴ) (unitaryHaarAdjointSketchLaw K n ell helln) μ := by
  have hl : HasLaw (Matrix.conjTranspose : Matrix (Fin n) (Fin ell) K → Matrix (Fin ell) (Fin n) K)
      (unitaryHaarAdjointSketchLaw K n ell helln) (unitaryHaarFrameMatrixLaw K n ell helln) :=
    ⟨Matrix.measurable_conjTranspose.aemeasurable,rfl⟩
  exact hl.fun_comp hZ

/-- The actual ambient law is supported on true orthonormal-column matrices. -/
theorem ae_hasOrthonormalCols_unitaryHaarFrameMatrixLaw
    {K : Type*} [RCLike K] {n ell : ℕ} (helln : ell≤n) :
    ∀ᵐ Z ∂unitaryHaarFrameMatrixLaw K n ell helln,HasOrthonormalCols Z := by
  rw [unitaryHaarFrameMatrixLaw,ae_map_iff measurable_subtype_coe.aemeasurable
    (p := fun Z : Matrix (Fin n) (Fin ell) K => HasOrthonormalCols Z)
      (isClosed_unitaryStiefel K n ell).measurableSet]
  exact ae_of_all _ (fun Z => Z.property)

/-- Exact native frame law supplies almost-sure orthonormal columns on every
sample space, without a separate orthogonality hypothesis. -/
theorem _root_.ProbabilityTheory.HasLaw.ae_hasOrthonormalCols_of_unitaryHaarFrameMatrixLaw
    {K Ω : Type*} [RCLike K] [MeasurableSpace Ω] {μ : Measure Ω} {n ell : ℕ}
    {Z : Ω → Matrix (Fin n) (Fin ell) K} {helln : ell≤n}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw K n ell helln) μ) :
    ∀ᵐ ω ∂μ,HasOrthonormalCols (Z ω) := by
  have h := ae_hasOrthonormalCols_unitaryHaarFrameMatrixLaw (K := K) helln
  rw [← hZ.map_eq] at h
  exact ae_of_ae_map hZ.aemeasurable h

/-- Transport any genuine native frame integral to an arbitrary sample space
with exactly the native ambient matrix law. This retains integrability as well
as the actual expectation value, including matrix-valued observables. -/
theorem integrable_and_integral_comp_unitaryHaarFrameMatrixLaw_of_hasLaw
    {K Ω E : Type*} [RCLike K] [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {n ell : ℕ} {helln : ell≤n}
    {Z : Ω → Matrix (Fin n) (Fin ell) K}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw K n ell helln) μ)
    (f : Matrix (Fin n) (Fin ell) K → E) (hf : Measurable f)
    (hframe : Integrable (fun Q : UnitaryStiefel K n ell => f Q.val)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (fun ω => f (Z ω)) μ ∧
      (∫ ω,f (Z ω) ∂μ)=∫ Q : UnitaryStiefel K n ell,f Q.val ∂unitaryHaarFrameLaw K n ell helln := by
  have hbase : Integrable f (unitaryHaarFrameMatrixLaw K n ell helln) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mpr hframe
  constructor
  · rw [← hZ.map_eq] at hbase
    exact hbase.comp_aemeasurable hZ.aemeasurable
  · exact (hZ.integral_comp hf.aestronglyMeasurable).trans
      (integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable)

/-- The same transport helper when the supplied random matrix already has the
native adjoint sketch law, so no sample-space frame construction is needed. -/
theorem integrable_and_integral_comp_unitaryHaarAdjointSketchLaw_of_hasLaw
    {K Ω E : Type*} [RCLike K] [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {n ell : ℕ} {helln : ell≤n}
    {S : Ω → Matrix (Fin ell) (Fin n) K}
    (hS : HasLaw S (unitaryHaarAdjointSketchLaw K n ell helln) μ)
    (f : Matrix (Fin ell) (Fin n) K → E) (hf : Measurable f)
    (hframe : Integrable (fun Q : UnitaryStiefel K n ell => f Q.valᴴ)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (fun ω => f (S ω)) μ ∧
      (∫ ω,f (S ω) ∂μ)=∫ Q : UnitaryStiefel K n ell,f Q.valᴴ ∂unitaryHaarFrameLaw K n ell helln := by
  have hm : Measurable (fun Z : Matrix (Fin n) (Fin ell) K => f Zᴴ) :=
    hf.comp Matrix.measurable_conjTranspose
  have hbase : Integrable f (unitaryHaarAdjointSketchLaw K n ell helln) := by
    apply (integrable_map_measure hf.aestronglyMeasurable Matrix.measurable_conjTranspose.aemeasurable).mpr
    exact (integrable_map_measure hm.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mpr hframe
  constructor
  · rw [← hS.map_eq] at hbase
    exact hbase.comp_aemeasurable hS.aemeasurable
  · apply (hS.integral_comp hf.aestronglyMeasurable).trans
    rw [unitaryHaarAdjointSketchLaw,integral_map Matrix.measurable_conjTranspose.aemeasurable hf.aestronglyMeasurable]
    exact integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable

end NLAlib

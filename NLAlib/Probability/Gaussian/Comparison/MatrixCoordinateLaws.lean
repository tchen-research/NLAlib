import NLAlib.Matrix.Functions.HermitianCoordinates
import NLAlib.Probability.Moments.MatrixDifference
import NLAlib.Probability.Exchangeable.ThirdCopyMoments
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Actual matrix laws in full real entry coordinates

The actual independent sum, its resampling triple, centered Gaussian laws,
and independent-copy Schatten moments commute with full real coordinates.
Hermitian reconstruction is used only after proving its almost-everywhere
identity on the original matrix laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- All finite norm moments pass to the actual full real-coordinate law. -/
theorem memLp_id_map_matrixRealCoordinates
    (ν : Measure M) [IsProbabilityMeasure ν] {p : ENNReal}
    (hν : MemLp (id : M → M) p ν) :
    MemLp (id : E → E) p (ν.map matrixRealCoordinates) := by
  have hm : MemLp (fun A : M => matrixRealCoordinates A) p ν := by
    simpa [matrixRealCoordinatesContinuousLinearEquiv, Function.comp_def] using
      (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap.comp_memLp' hν
  exact (memLp_map_measure_iff (f := (matrixRealCoordinates : M → E))
    (g := (id : E → E)) aestronglyMeasurable_id
      (measurable_matrixRealCoordinates (m := n) (n := n)).aemeasurable).mpr hm

open scoped Matrix.Norms.L2Operator in
/-- Coordinatewise realification transports the complete independent product
law, retaining mixed real and imaginary covariances. -/
theorem hasLaw_matrixRealCoordinates_pi
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (fun x : ι → M => fun i => matrixRealCoordinates (x i))
      (Measure.pi fun i => (ν i).map matrixRealCoordinates) (Measure.pi ν) := by
  refine ⟨(measurable_pi_lambda _ (fun i =>
    (measurable_matrixRealCoordinates.comp (measurable_pi_apply i)))).aemeasurable, ?_⟩
  exact Measure.pi_map_pi (fun i =>
    measurable_matrixRealCoordinates.aemeasurable)

open scoped Matrix.Norms.L2Operator in
/-- The full coordinates of an actual independent matrix sum have the sum law
of the independent actual full-coordinate marginals. -/
theorem hasLaw_matrixRealCoordinates_sum_pi
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (fun x : ι → M => matrixRealCoordinates (∑ i, x i))
      ((Measure.pi fun i => (ν i).map matrixRealCoordinates).map
        (fun x : ι → E => ∑ i, x i)) (Measure.pi ν) := by
  have hs : HasLaw (fun x : ι → E => ∑ i, x i)
      ((Measure.pi fun i => (ν i).map matrixRealCoordinates).map
        (fun x : ι → E => ∑ i, x i))
      (Measure.pi fun i => (ν i).map matrixRealCoordinates) := ⟨by fun_prop, rfl⟩
  simpa only [Function.comp_def, map_sum] using hs.comp (hasLaw_matrixRealCoordinates_pi ν)

open scoped Matrix.Norms.L2Operator in
/-- Almost-everywhere Hermitian support is preserved by finite independent
sums on the actual product law. -/
theorem ae_isHermitian_sum_pi
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian) :
    ∀ᵐ x : ι → M ∂Measure.pi ν, (∑ i, x i).IsHermitian := by
  have hh : ∀ᵐ x : ι → M ∂Measure.pi ν, ∀ i, (x i).IsHermitian :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hν i))
  filter_upwards [hh] with x hx
  exact isSelfAdjoint_sum _ (fun i _ => hx i)

open scoped Matrix.Norms.L2Operator in
/-- The actual full-coordinate law reconstructs to its original Hermitian
matrix law, with an almost-everywhere support condition. -/
theorem map_hermitianMatrixFromRealCoordinates_map_matrixRealCoordinates
    (ν : Measure M) (hν : ∀ᵐ A ∂ν, A.IsHermitian) :
    (ν.map matrixRealCoordinates).map hermitianMatrixFromRealCoordinates = ν := by
  rw [Measure.map_map hermitianMatrixFromRealCoordinates.continuous.measurable
    measurable_matrixRealCoordinates]
  calc
    _ = ν.map id := Measure.map_congr (hν.mono fun A hA =>
      hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA)
    _ = ν := Measure.map_id

open scoped Matrix.Norms.L2Operator in
/-- Hermitian reconstruction preserves the exact original normalized
independent-copy Schatten third-moment parameter. -/
theorem matrixDifferenceThirdMoment_map_matrixRealCoordinates_reconstruct
    (ν : ι → Measure M) (hν : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian) :
    matrixDifferenceThirdMoment (fun i =>
      ((ν i).map matrixRealCoordinates).map hermitianMatrixFromRealCoordinates) =
      matrixDifferenceThirdMoment ν := by
  have he : (fun i => ((ν i).map matrixRealCoordinates).map
      hermitianMatrixFromRealCoordinates) = ν := by
    funext i
    exact map_hermitianMatrixFromRealCoordinates_map_matrixRealCoordinates (ν i) (hν i)
  rw [he]

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

open scoped Matrix.Norms.L2Operator in
/-- The actual coordinate resampling sum and actual original matrix sum have
identical laws in full real coordinates. -/
theorem identDistrib_resamplingTripleOriginal_matrixRealCoordinates_sum
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)] :
    IdentDistrib (resamplingTripleOriginal :
      ι × ((ι × Fin 3) → E) → E)
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i))
      (resamplingTripleMeasure fun i => (ν i).map matrixRealCoordinates) (Measure.pi ν) := by
  haveI (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  have ht := hasLaw_resamplingTripleOriginal (fun i => (ν i).map matrixRealCoordinates)
  have hs := hasLaw_matrixRealCoordinates_sum_pi ν
  exact ⟨ht.aemeasurable, hs.aemeasurable, ht.map_eq.trans hs.map_eq.symm⟩

open scoped Matrix.Norms.L2Operator in
/-- The resampling coordinate mean is exactly the full real coordinates of
the actual independent matrix sum mean. -/
theorem integral_resamplingTripleOriginal_matrixRealCoordinates
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : M → M) 3 (ν i)) :
    (∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure
        (fun i => (ν i).map matrixRealCoordinates)) =
      matrixRealCoordinates (∫ x : ι → M, ∑ i, x i ∂Measure.pi ν) := by
  have hi (i : ι) : Integrable (fun x : ι → M => x i) (Measure.pi ν) :=
    integrable_eval (μ := ν) (i := i) ((hν i).integrable (by norm_num))
  have hs : Integrable (fun x : ι → M => ∑ i, x i) (Measure.pi ν) := by
    simpa using integrable_finsetSum Finset.univ (fun i _ => hi i)
  exact (identDistrib_resamplingTripleOriginal_matrixRealCoordinates_sum ν).integral_eq.trans
    ((matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap.integral_comp_comm hs)

open scoped Matrix.Norms.L2Operator in
/-- Full scalar coordinate covariances of the resampling sum are the actual
full real-entry covariances of the original independent matrix sum. -/
theorem covariance_resamplingTripleOriginal_matrixRealCoordinates
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)] (a b : J) :
    cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p a),
        (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p b);
        resamplingTripleMeasure (fun i => (ν i).map matrixRealCoordinates)] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν] := by
  haveI (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  have ht := hasLaw_resamplingTripleOriginal (fun i => (ν i).map matrixRealCoordinates)
  have hs := hasLaw_matrixRealCoordinates_sum_pi ν
  exact (ht.covariance_fun_comp (measurable_pi_apply a).aemeasurable
    (measurable_pi_apply b).aemeasurable).trans
      (hs.covariance_fun_comp (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable).symm

end NLAlib

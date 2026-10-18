import NLAlib.ForMathlib.Probability.GaussianCoordinates
import NLAlib.Matrix.Basic.RealCoordinates
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian matrix sums and full covariance

Finite independent Gaussian matrix sums are Gaussian. Full real and imaginary
entry covariances add under independence and determine the Gaussian matrix
law uniquely. These bridges identify the sum of individual Gaussian proxies
with the Gaussian proxy specified by the covariance of the original sum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Gaussian matrix laws are uniquely determined by their matrix mean and all
mixed real and imaginary entry covariances. Singular covariance is allowed. -/
theorem gaussian_matrix_eq_of_mean_covariance_eq
    (μ ν : Measure M) [IsGaussian μ] [IsGaussian ν]
    (hmean : (∫ A, A ∂μ) = ∫ A, A ∂ν)
    (hcov : ∀ i j : J,
      cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; μ] =
        cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; ν]) :
    μ = ν := by
  let L := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  apply L.toHomeomorph.measurableEmbedding.map_injective
  change μ.map L = ν.map L
  apply IsGaussian.ext_of_pi_mean_covariance_eq
  · rw [L.integral_id_map, L.integral_id_map, hmean]
  · intro i j
    rw [covariance_map_fun (continuous_apply i).aestronglyMeasurable
        (continuous_apply j).aestronglyMeasurable L.continuous.measurable.aemeasurable,
      covariance_map_fun (continuous_apply i).aestronglyMeasurable
        (continuous_apply j).aestronglyMeasurable L.continuous.measurable.aemeasurable]
    exact hcov i j

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Under independence every full real-entry covariance of a matrix sum is
the sum of the corresponding covariances of its summands. No Gaussianity or
self-adjointness is needed for this identity. -/
theorem covariance_matrixRealCoordinates_sum_eq_sum
    (X : ι → Ω → M) (hX : ∀ k, MemLp (fun ω => matrixRealCoordinates (X k ω)) 2 P)
    (hind : iIndepFun X P) (i j : J) :
    cov[fun ω => matrixRealCoordinates (∑ k, X k ω) i,
      fun ω => matrixRealCoordinates (∑ k, X k ω) j; P] =
        ∑ k, cov[fun ω => matrixRealCoordinates (X k ω) i,
          fun ω => matrixRealCoordinates (X k ω) j; P] := by
  classical
  simp only [map_sum, Finset.sum_apply]
  rw [covariance_fun_sum_fun_sum (fun k => (hX k).eval i) (fun k => (hX k).eval j)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_eq_single k
  · intro l _ hlk
    have hh := (hind.indepFun hlk.symm).comp
      (show Measurable (fun A : M => matrixRealCoordinates A i) from by fun_prop)
      (show Measurable (fun A : M => matrixRealCoordinates A j) from by fun_prop)
    exact hh.covariance_eq_zero ((hX k).eval i) ((hX l).eval j)
  · simp

open scoped Matrix.Norms.L2Operator in
/-- The sum map on the finite product of arbitrary Gaussian matrix laws has
a Gaussian law. This includes an empty family and singular summands. -/
theorem isGaussian_map_sum_pi (γ : ι → Measure M) [∀ k, IsGaussian (γ k)] :
    IsGaussian ((Measure.pi γ).map (fun x : ι → M => ∑ k, x k)) := by
  have hLaw (k : ι) : HasLaw (fun x : ι → M => x k) (γ k) (Measure.pi γ) :=
    (measurePreserving_eval γ k).hasLaw
  have hInd : iIndepFun (fun k (x : ι → M) => x k) (Measure.pi γ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  exact (hInd.hasGaussianLaw_fun_sum (fun k => (hLaw k).hasGaussianLaw)).isGaussian_map

open scoped Matrix.Norms.L2Operator in
/-- The mean of a finite sum under its independent product law is the sum of
the means of its Gaussian marginals. -/
theorem integral_sum_pi_gaussian (γ : ι → Measure M) [∀ k, IsGaussian (γ k)] :
    (∫ x : ι → M, ∑ k, x k ∂Measure.pi γ) = ∑ k, ∫ A, A ∂γ k := by
  rw [integral_finsetSum Finset.univ (f := fun k (x : ι → M) => x k) (fun k _ =>
    integrable_eval (IsGaussian.integrable_id (μ := γ k)))]
  simp only [integral_eval]

open scoped Matrix.Norms.L2Operator in
/-- The mean of the actual Gaussian sum law is the sum of its marginal means. -/
theorem integral_id_map_sum_pi_gaussian (γ : ι → Measure M) [∀ k, IsGaussian (γ k)] :
    (∫ A, A ∂(Measure.pi γ).map (fun x : ι → M => ∑ k, x k)) =
      ∑ k, ∫ A, A ∂γ k := by
  have hi := integral_map (by fun_prop : AEMeasurable (fun x : ι → M => ∑ k, x k)
      (Measure.pi γ)) aestronglyMeasurable_id
  simpa only [id_eq] using hi.trans (integral_sum_pi_gaussian γ)

open scoped Matrix.Norms.L2Operator in
/-- Every full real-entry covariance of the actual Gaussian sum law equals
the sum of its marginal covariances. -/
theorem covariance_matrixRealCoordinates_map_sum_pi_eq_sum
    (γ : ι → Measure M) [∀ k, IsGaussian (γ k)] (i j : J) :
    cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j;
      (Measure.pi γ).map (fun x : ι → M => ∑ k, x k)] =
      ∑ k, cov[fun A => matrixRealCoordinates A i,
        fun A => matrixRealCoordinates A j; γ k] := by
  have hLaw (k : ι) : HasLaw (fun x : ι → M => x k) (γ k) (Measure.pi γ) :=
    (measurePreserving_eval γ k).hasLaw
  have hInd : iIndepFun (fun k (x : ι → M) => x k) (Measure.pi γ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hX (k : ι) : MemLp (fun x : ι → M => matrixRealCoordinates (x k)) 2
      (Measure.pi γ) :=
    (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap
      |>.comp_memLp' (hLaw k).hasGaussianLaw.memLp_two
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  rw [covariance_matrixRealCoordinates_sum_eq_sum (fun k (x : ι → M) => x k) hX hInd]
  apply Finset.sum_congr rfl
  intro k _
  have hc := covariance_map_fun
    (μ := Measure.pi γ)
    (Z := fun x : ι → M => x k)
    (X := fun A : M => matrixRealCoordinates A i)
    (Y := fun A : M => matrixRealCoordinates A j)
    (by fun_prop) (by fun_prop) (measurable_pi_apply k).aemeasurable
  rw [(measurePreserving_eval γ k).map_eq] at hc
  exact hc.symm

open scoped Matrix.Norms.L2Operator in
/-- The independent sum of centered Gaussian proxy laws equals any centered
Gaussian matrix law whose full covariance is the sum of their covariances.
This identifies the law appearing after successive one-summand replacements. -/
theorem map_sum_pi_gaussian_eq_of_covariance_eq
    (γ : ι → Measure M) [∀ k, IsGaussian (γ k)]
    (ν : Measure M) [IsGaussian ν]
    (hmean : ∀ k, (∫ A, A ∂γ k) = 0) (hνmean : (∫ A, A ∂ν) = 0)
    (hcov : ∀ i j : J,
      (∑ k, cov[fun A => matrixRealCoordinates A i,
        fun A => matrixRealCoordinates A j; γ k]) =
          cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; ν]) :
    (Measure.pi γ).map (fun x : ι → M => ∑ k, x k) = ν := by
  have : IsGaussian ((Measure.pi γ).map (fun x : ι → M => ∑ k, x k)) :=
    isGaussian_map_sum_pi γ
  apply gaussian_matrix_eq_of_mean_covariance_eq
  · rw [integral_id_map_sum_pi_gaussian, hνmean]
    simp only [hmean, Finset.sum_const_zero]
  · intro i j
    rw [covariance_matrixRealCoordinates_map_sum_pi_eq_sum]
    exact hcov i j

open scoped Matrix.Norms.L2Operator in
/-- Independent sums of almost surely Hermitian marginals remain almost
surely Hermitian under the actual sum law. Gaussianity is not required. -/
theorem ae_isHermitian_map_sum_pi (γ : ι → Measure M) [∀ k, IsProbabilityMeasure (γ k)]
    (hHerm : ∀ k, ∀ᵐ A ∂γ k, A.IsHermitian) :
    ∀ᵐ A ∂(Measure.pi γ).map (fun x : ι → M => ∑ k, x k), A.IsHermitian := by
  have hclosed : MeasurableSet {A : M | A.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun A : M => Aᴴ)) continuous_id).measurableSet
  apply (ae_map_iff (μ := Measure.pi γ)
    (f := fun x : ι → M => ∑ k, x k) (by fun_prop) hclosed).mpr
  have heval (k : ι) : ∀ᵐ x : ι → M ∂Measure.pi γ, (x k).IsHermitian := by
    apply (ae_map_iff (measurable_pi_apply k).aemeasurable hclosed).mp
    rw [(measurePreserving_eval γ k).map_eq]
    exact hHerm k
  filter_upwards [ae_all_iff.mpr heval] with x hx
  change (∑ k, x k)ᴴ = ∑ k, x k
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k _ => hx k)

end NLAlib

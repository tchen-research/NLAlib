import NLAlib.Probability.Gaussian.Basic.CovarianceRepresentation
import NLAlib.ForMathlib.Probability.QuadraticCovariance
import NLAlib.Matrix.Functions.HermitianCoordinates
import Mathlib.Probability.HasLaw

/-!
# Centered Gaussian proxies with prescribed full covariance

Every square-integrable finite real-coordinate law has a centered Gaussian
proxy with exactly the same full covariance, including singular covariance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

set_option backward.isDefEq.respectTransparency false in
/-- Every finite-dimensional real-coordinate law with finite second moments has
a centered Gaussian proxy matching every coordinate covariance. The original
law itself need not be Gaussian or have a nonsingular covariance matrix. -/
theorem exists_isGaussian_integral_eq_zero_covariance_eq {κ : Type*}
    [Fintype κ] [DecidableEq κ] (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) :
    ∃ ν : Measure (κ → ℝ), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      ∀ i j, cov[(fun x => x i), (fun x => x j); ν] =
        cov[(fun x => x i), (fun x => x j); μ] := by
  let e : EuclideanSpace ℝ κ ≃L[ℝ] (κ → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)
  let μE : Measure (EuclideanSpace ℝ κ) := μ.map e.symm
  have : IsProbabilityMeasure μE := μ.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable
  have hμE : MemLp id 2 μE := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id
      e.symm.continuous.measurable.aemeasurable).mpr
    exact e.symm.toContinuousLinearMap.comp_memLp' hμ
  let γ : Measure (EuclideanSpace ℝ κ) := multivariateGaussian 0 (gaussianCovarianceMatrix μE)
  have : IsGaussian γ := inferInstanceAs (IsGaussian (multivariateGaussian _ _))
  let ν := γ.map e
  have : IsGaussian ν := inferInstanceAs (IsGaussian (γ.map e.toContinuousLinearMap))
  refine ⟨ν, inferInstance, ?_, ?_⟩
  · change (∫ x, x ∂γ.map e) = 0
    rw [show (∫ x, x ∂γ.map e) = ∫ x, e x ∂γ from
      integral_map e.continuous.measurable.aemeasurable (by fun_prop)]
    have he := e.toContinuousLinearMap.integral_comp_comm
      (show Integrable (fun x : EuclideanSpace ℝ κ => x) γ from IsGaussian.integrable_fun_id)
    change (∫ x, e x ∂γ) = e (∫ x, x ∂γ) at he
    rw [he]
    simp only [γ, integral_id_multivariateGaussian, map_zero]
  · intro i j
    have hγlaw : HasLaw e ν γ := ⟨e.continuous.measurable.aemeasurable, rfl⟩
    have hμlaw : HasLaw e.symm μE μ := ⟨e.symm.continuous.measurable.aemeasurable, rfl⟩
    have h1 := hγlaw.covariance_fun_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable
    have h2 := hμlaw.covariance_fun_comp (by fun_prop : Measurable fun x : EuclideanSpace ℝ κ => x i).aemeasurable
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ κ => x j).aemeasurable
    rw [← h1]
    change cov[(fun x : EuclideanSpace ℝ κ => x i), (fun x => x j); γ] = _
    rw [covariance_eval_multivariateGaussian (gaussianCovarianceMatrix_posSemidef μE),
      gaussianCovarianceMatrix_apply μE hμE]
    exact h2.symm

open scoped Matrix.Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/-- A centered square-integrable Hermitian matrix law has an actual centered
Gaussian Hermitian proxy matching its entire real and imaginary entry
covariance tensor. Singular covariance and the empty matrix dimension are
included. The support condition is obtained by the genuine linear Hermitian
projection, rather than assumed for the new Gaussian law.
Source: the Gaussian covariance proxy used in Tropp's BMV replacement theorem.
atlas: gaussian-trace-mgf-comparison (partial) -/
theorem exists_isGaussian_hermitian_integral_eq_zero_covariance_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (μ : Measure (Matrix n n ℂ)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun A : Matrix n n ℂ => matrixRealCoordinates A) 2 μ)
    (hmean : (∫ A, A ∂μ) = 0) (hherm : ∀ᵐ A ∂μ, A.IsHermitian) :
    ∃ ν : Measure (Matrix n n ℂ), IsGaussian ν ∧ (∫ A, A ∂ν) = 0 ∧
      (∀ᵐ A ∂ν, A.IsHermitian) ∧
      ∀ i j : (n × n) ⊕ (n × n),
        cov[(fun A => matrixRealCoordinates A i), (fun A => matrixRealCoordinates A j); ν] =
          cov[(fun A => matrixRealCoordinates A i), (fun A => matrixRealCoordinates A j); μ] := by
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  let P := hermitianMatrixFromRealCoordinates (n := n)
  let ρ := μ.map C
  have : IsProbabilityMeasure ρ := μ.isProbabilityMeasure_map C.continuous.measurable.aemeasurable
  have hρ : MemLp id 2 ρ := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id C.continuous.measurable.aemeasurable).mpr
    exact hμ
  have hμint : Integrable (fun A : Matrix n n ℂ => A) μ := by
    have hi := C.symm.toContinuousLinearMap.comp_memLp' hμ
    have he (A : Matrix n n ℂ) : C.symm (matrixRealCoordinates A) = A :=
      matrixRealCoordinates.symm_apply_apply A
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, he] using hi.integrable (by norm_num)
  have hρmean : (∫ x, x ∂ρ) = 0 := by
    change (∫ x, x ∂μ.map C) = 0
    rw [show (∫ x, x ∂μ.map C) = ∫ A, C A ∂μ from
      integral_map C.continuous.measurable.aemeasurable (by fun_prop)]
    rw [show (∫ A, C A ∂μ) = C (∫ A, A ∂μ) from
      C.toContinuousLinearMap.integral_comp_comm hμint]
    rw [hmean, map_zero]
  obtain ⟨γ, hγ, hγmean, hγcov⟩ := exists_isGaussian_integral_eq_zero_covariance_eq ρ hρ
  have : IsGaussian γ := hγ
  let ν := γ.map P
  have : IsGaussian ν := inferInstanceAs (IsGaussian (γ.map P))
  have hνmean : (∫ A, A ∂ν) = 0 := by
    change (∫ A, A ∂γ.map P) = 0
    rw [show (∫ A, A ∂γ.map P) = ∫ x, P x ∂γ from
      integral_map P.continuous.measurable.aemeasurable (by fun_prop)]
    rw [show (∫ x, P x ∂γ) = P (∫ x, x ∂γ) from
      P.integral_comp_comm IsGaussian.integrable_fun_id]
    rw [hγmean, map_zero]
  have hνherm : ∀ᵐ A ∂ν, A.IsHermitian := by
    apply (ae_map_iff P.continuous.measurable.aemeasurable ?_).mpr
    · exact Filter.Eventually.of_forall isHermitian_hermitianMatrixFromRealCoordinates
    · exact (isClosed_eq (by fun_prop : Continuous (fun A : Matrix n n ℂ => Aᴴ))
        continuous_id).measurableSet
  have hρP : HasLaw P μ ρ := by
    refine ⟨P.continuous.measurable.aemeasurable, ?_⟩
    change (μ.map C).map P = μ
    rw [Measure.map_map P.continuous.measurable C.continuous.measurable]
    have he : P ∘ C =ᵐ[μ] id := hherm.mono fun A hA =>
      hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA
    rw [Measure.map_congr he, Measure.map_id]
  have hνP : HasLaw P ν γ := ⟨P.continuous.measurable.aemeasurable, rfl⟩
  refine ⟨ν, inferInstance, hνmean, hνherm, ?_⟩
  intro i j
  let Li := (ContinuousLinearMap.proj i).comp (C.toContinuousLinearMap.comp P)
  let Lj := (ContinuousLinearMap.proj j).comp (C.toContinuousLinearMap.comp P)
  have hsame := covariance_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    γ ρ IsGaussian.memLp_two_id hρ (hγmean.trans hρmean.symm) hγcov Li Lj
  have hνcov := hνP.covariance_fun_comp
    (by fun_prop : Measurable (fun A : Matrix n n ℂ => matrixRealCoordinates A i)).aemeasurable
    (by fun_prop : Measurable (fun A : Matrix n n ℂ => matrixRealCoordinates A j)).aemeasurable
  have hμcov := hρP.covariance_fun_comp
    (by fun_prop : Measurable (fun A : Matrix n n ℂ => matrixRealCoordinates A i)).aemeasurable
    (by fun_prop : Measurable (fun A : Matrix n n ℂ => matrixRealCoordinates A j)).aemeasurable
  exact hνcov.symm.trans (hsame.trans hμcov)

end NLAlib

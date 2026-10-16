import NLAlib.Probability.Gaussian.Comparison.MatrixCoordinateLaws

/-! # Actual centered real-coordinate Gaussian matrix laws

A genuine Gaussian full real-coordinate law can be centered without changing
its covariance tensor. The mean and covariance assertions below are actual
Bochner integrals and scalar covariances of the pushforward measure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- Center an actual matrix law in all real and imaginary entry coordinates. -/
def centeredMatrixCoordinateLaw (ρ : Measure M) : Measure E :=
  ρ.map (fun A : M => matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ)

open scoped Matrix.Norms.L2Operator in
/-- The centered full-coordinate map has its actual pushforward law. -/
theorem hasLaw_centeredMatrixCoordinates (ρ : Measure M) :
    HasLaw (fun A : M => matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ)
      (centeredMatrixCoordinateLaw ρ) ρ := ⟨by fun_prop, rfl⟩

open scoped Matrix.Norms.L2Operator in
/-- A matrix with a genuine Gaussian full-coordinate law is integrable itself;
no separate matrix moment assumption is required. -/
theorem integrable_id_of_hasGaussianLaw_matrixRealCoordinates
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ) :
    Integrable (fun A : M => A) ρ := by
  have hi := (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm.toContinuousLinearMap.integrable_comp
    hρ.integrable
  have he (A : M) :
      (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).symm
        (matrixRealCoordinates A) = A :=
    (matrixRealCoordinates : M ≃ₗ[ℝ] E).symm_apply_apply A
  simpa only [ContinuousLinearEquiv.coe_coe, he] using hi

open scoped Matrix.Norms.L2Operator in
/-- Centering preserves the native full Gaussian law, including singular
covariance matrices. -/
theorem hasGaussianLaw_id_centeredMatrixCoordinateLaw
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ) :
    HasGaussianLaw (id : E → E) (centeredMatrixCoordinateLaw ρ) := by
  have he : centeredMatrixCoordinateLaw ρ =
      (ρ.map matrixRealCoordinates).map
        (fun x : E => x - ∫ B : M, matrixRealCoordinates B ∂ρ) := by
    rw [Measure.map_map (by fun_prop)
      measurable_matrixRealCoordinates]
    rfl
  rw [he]
  haveI := hρ.isGaussian_map
  exact IsGaussian.hasGaussianLaw_id

open scoped Matrix.Norms.L2Operator in
/-- Every scalar coordinate of the actual centered Gaussian law has mean zero. -/
theorem integral_eval_centeredMatrixCoordinateLaw_eq_zero
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ) (a : J) :
    (∫ z : E, z a ∂centeredMatrixCoordinateLaw ρ) = 0 := by
  haveI := hρ.isProbabilityMeasure
  have ht := (hasLaw_centeredMatrixCoordinates ρ).integral_comp
    (measurable_pi_apply a).stronglyMeasurable.aestronglyMeasurable
  have he : (∫ B : M, matrixRealCoordinates B ∂ρ) a =
      ∫ B : M, matrixRealCoordinates B a ∂ρ :=
    ((ContinuousLinearMap.proj a : E →L[ℝ] ℝ).integral_comp_comm hρ.integrable).symm
  rw [← ht]
  change (∫ A : M, matrixRealCoordinates A a - (∫ B : M, matrixRealCoordinates B ∂ρ) a ∂ρ) = 0
  rw [integral_sub (hρ.eval a).integrable (integrable_const _), integral_const,
    probReal_univ, one_smul, he, sub_self]

open scoped Matrix.Norms.L2Operator in
/-- Centering changes none of the actual full real-entry covariance tensor. -/
theorem covariance_eval_centeredMatrixCoordinateLaw
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ) (a b : J) :
    cov[(fun z : E => z a), (fun z : E => z b); centeredMatrixCoordinateLaw ρ] =
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b); ρ] := by
  haveI := hρ.isProbabilityMeasure
  have ht := (hasLaw_centeredMatrixCoordinates ρ).covariance_fun_comp
    (measurable_pi_apply a).aemeasurable
    (measurable_pi_apply b).aemeasurable
  change cov[(fun A : M => matrixRealCoordinates A a - _),
    (fun A : M => matrixRealCoordinates A b - _); ρ] = _ at ht
  rw [covariance_sub_const_left (hρ.eval a).integrable,
    covariance_sub_const_right (hρ.eval b).integrable] at ht
  exact ht.symm

end NLAlib

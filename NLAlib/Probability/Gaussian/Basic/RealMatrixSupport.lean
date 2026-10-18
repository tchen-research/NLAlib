import NLAlib.ForMathlib.Analysis.Matrix.ComplexParts
import NLAlib.Matrix.Basic.RealCoordinates
import NLAlib.Matrix.Norms.Complexification
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.Variance

/-!
# Real support of a complex Gaussian covariance proxy

When full covariance matching gives zero variance to every imaginary entry,
a centered complex Gaussian matrix is real almost surely. Its entrywise real
part is an actual centered real Gaussian matrix, preserves Hermitian support,
and has exactly the same expected spectral norm. Thus real covariance problems
can use a real sphere net without doubling their dimension.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A centered complex Gaussian matrix with zero imaginary-entry variances
is almost surely exactly the complexification of its real part. -/
theorem ae_eq_map_ofReal_reCLM_of_im_variance_eq_zero
    (γ : Measure (Matrix n n ℂ)) [IsGaussian γ]
    (hmean : (∫ A, A ∂γ) = 0)
    (hvar : ∀ i j, Var[fun A => (A i j).im; γ] = 0) :
    ∀ᵐ A ∂γ, (Matrix.reCLM A).map Complex.ofReal = A := by
  have hi (i j : n) : ∀ᵐ A ∂γ, (A i j).im = 0 := by
    let L : Matrix n n ℂ →L[ℝ] ℝ := Complex.imCLM.comp
      (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
    have hLp : MemLp (fun A : Matrix n n ℂ => (A i j).im) 2 γ :=
      L.comp_memLp' (IsGaussian.memLp_two_id (μ := γ))
    have hm : (∫ A, (A i j).im ∂γ) = 0 := by
      have h := L.integral_comp_comm (IsGaussian.integrable_id (μ := γ))
      simpa only [id_eq, hmean, map_zero, L, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', Matrix.entryLinearMap_apply,
        Complex.imCLM_apply] using h
    simpa only [hm] using ae_eq_integral_of_variance_eq_zero hLp (hvar i j)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hi i)] with A hA
  exact Matrix.map_ofReal_reCLM_of_im_eq_zero A hA

omit [Fintype n] [DecidableEq n] in
/-- Matching the full real-entry covariance of a real matrix law forces
every imaginary-entry variance of its complex Gaussian proxy to vanish. -/
theorem im_variance_eq_zero_of_covariance_eq_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℝ) (γ : Measure (Matrix n n ℂ)) [IsGaussian γ]
    (hcov : ∀ i j : (n × n) ⊕ (n × n),
      cov[fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) i,
        fun ω => matrixRealCoordinates ((X ω).map Complex.ofReal) j; μ] =
      cov[fun A => matrixRealCoordinates A i, fun A => matrixRealCoordinates A j; γ])
    (i j : n) : Var[fun A => (A i j).im; γ] = 0 := by
  have hc := hcov (Sum.inr (i, j)) (Sum.inr (i, j))
  simp only [matrixRealCoordinates_inr, Matrix.map_apply, Complex.ofReal_im,
    covariance_const_left] at hc
  have hs := covariance_self (μ := γ) (X := fun A : Matrix n n ℂ => (A i j).im)
    ((Complex.measurable_im.comp (Matrix.measurable_entry i j)).aemeasurable)
  exact hs.symm.trans hc.symm

open scoped Matrix.Norms.L2Operator in
/-- The real-part law of a centered Gaussian Hermitian matrix is an actual
centered real Gaussian symmetric matrix law, including singular covariance. -/
theorem isGaussian_integral_eq_zero_ae_isHermitian_map_reCLM
    (γ : Measure (Matrix n n ℂ)) [IsGaussian γ]
    (hmean : (∫ A, A ∂γ) = 0) (hHerm : ∀ᵐ A ∂γ, A.IsHermitian) :
    IsGaussian (γ.map (Matrix.reCLM (m := n) (n := n))) ∧
      (∫ A, A ∂γ.map (Matrix.reCLM (m := n) (n := n))) = 0 ∧
      ∀ᵐ A ∂γ.map (Matrix.reCLM (m := n) (n := n)), A.IsHermitian := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Matrix.reCLM.integral_id_map (IsGaussian.integrable_id (μ := γ)), hmean, map_zero]
  · apply (ae_map_iff (by fun_prop) ?_).mpr
    · exact hHerm.mono fun A hA => hA.reCLM
    · exact (isClosed_eq (by fun_prop : Continuous (fun A : Matrix n n ℝ => Aᴴ))
        continuous_id).measurableSet

open scoped Matrix.Norms.L2Operator in
/-- Taking the real-part law preserves the actual expected spectral norm
when the centered Gaussian has zero imaginary-entry variances. -/
theorem integral_specNorm_eq_integral_specNorm_map_reCLM_of_im_variance_eq_zero
    (γ : Measure (Matrix n n ℂ)) [IsGaussian γ]
    (hmean : (∫ A, A ∂γ) = 0)
    (hvar : ∀ i j, Var[fun A => (A i j).im; γ] = 0) :
    (∫ A, specNorm A ∂γ) =
      ∫ A, specNorm A ∂γ.map (Matrix.reCLM (m := n) (n := n)) := by
  have hcont : Continuous (specNorm : Matrix n n ℝ → ℝ) := by
    change Continuous (fun A : Matrix n n ℝ => specNorm A)
    simp only [specNorm_eq_norm]
    exact continuous_norm
  rw [integral_map (by fun_prop) hcont.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_eq_map_ofReal_reCLM_of_im_variance_eq_zero γ hmean hvar] with A hA
  have h := specNorm_map_ofReal (𝕜 := ℂ) (Matrix.reCLM A)
  have heq : ((Matrix.reCLM A).map (algebraMap ℝ ℂ)) = A := by
    change ((Matrix.reCLM A).map Complex.ofReal) = A
    exact hA
  rw [heq] at h
  exact h

end NLAlib

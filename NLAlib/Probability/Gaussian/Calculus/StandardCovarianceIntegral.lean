import NLAlib.Probability.Gaussian.Calculus.CovarianceIntegral
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Exact covariance integral on actual independent standard coordinates

Both the mean and Kronecker-delta covariance are derived from the canonical
Gaussian product law before specializing the native covariance identity.
Source: arXiv:2108.06312v2, Corollary 4.12.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {κ F G : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
local notation "E" => κ → ℝ

local instance standard_isGaussian : IsGaussian (gaussianVector κ) := by
  have h := (hasGaussianLaw_id_gaussianVector κ).isGaussian_map
  change IsGaussian ((gaussianVector κ).map id) at h
  rwa [Measure.map_id] at h

omit [DecidableEq κ] in
private theorem standard_integral_id : (∫ x : E, x ∂gaussianVector κ) = 0 := by
  have hi := (hasGaussianLaw_id_gaussianVector κ).memLp_two.integrable one_le_two
  ext k
  have he := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).integral_comp_comm hi
  have hz := integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)
  simpa only [ContinuousLinearMap.proj_apply, Pi.zero_apply] using he.symm.trans hz

private theorem standard_covariance (i j : κ) :
    cov[(fun x : E => x i), (fun x : E => x j); gaussianVector κ] =
      if i = j then 1 else 0 := by
  rw [covariance_eq_sub (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i))
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j))]
  simp only [Pi.mul_apply]
  rw [integral_mul_apply_gaussianVector,
    integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i),
    zero_mul, sub_zero]

omit [DecidableEq κ] in
/-- The literal Gaussian correlation path has its genuine common marginal.
This is proved by an actual orthogonal rotation of two independent canonical
Gaussian vectors, including the endpoint correlations and empty dimensions. -/
theorem measurePreserving_standardGaussianCorrelation (t : ℝ)
    (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    MeasurePreserving (fun q : E × E => t • q.1 + Real.sqrt (1 - t ^ 2) • q.2)
      ((gaussianVector κ).prod (gaussianVector κ)) (gaussianVector κ) := by
  let θ := Real.arccos t
  have hr : MeasurePreserving (ContinuousLinearMap.rotation θ)
      ((gaussianVector κ).prod (gaussianVector κ))
      ((gaussianVector κ).prod (gaussianVector κ)) :=
    ⟨(ContinuousLinearMap.rotation θ).continuous.measurable,
      IsGaussian.map_rotation_eq_self standard_integral_id θ⟩
  have h := (measurePreserving_fst (μ := gaussianVector κ) (ν := gaussianVector κ)).comp hr
  simpa only [Function.comp_def, ContinuousLinearMap.rotation_apply, θ,
    Real.cos_arccos ht ht1, Real.sin_arccos] using h

/-- The exact bilinear covariance formula under actual independent standard
Gaussian coordinates. Its covariance contraction is the literal single
coordinate-gradient sum, including an empty coordinate family. All Gaussian
law, centering, and covariance identities are proved from the canonical law.
Source: arXiv:2108.06312v2, Corollary 4.12. -/
theorem integral_bilin_sub_bilin_integrals_eq_standard_gaussian_gradient_integral
    (f : E → F) (df : E → E →L[ℝ] F)
    (g : E → G) (dg : E → E →L[ℝ] G)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdfc : Continuous df)
    (hg : ∀ x, HasFDerivAt g (dg x) x) (hdgc : Continuous dg)
    (Cf Cd Cg Ce : ℝ) (hfb : ∀ x, ‖f x‖ ≤ Cf) (hdfb : ∀ x, ‖df x‖ ≤ Cd)
    (hgb : ∀ x, ‖g x‖ ≤ Cg) (hdgb : ∀ x, ‖dg x‖ ≤ Ce)
    (B : F →L[ℝ] G →L[ℝ] ℂ) :
    (∫ y : E, B (f y) (g y) ∂gaussianVector κ) -
        B (∫ y : E, f y ∂gaussianVector κ) (∫ y : E, g y ∂gaussianVector κ) =
      ∫ t : ℝ in (0 : ℝ)..1, ∑ k,
        ∫ q : E × E, B (df q.1 (Pi.single k 1))
          (dg (t • q.1 + Real.sqrt (1 - t ^ 2) • q.2) (Pi.single k 1))
            ∂(gaussianVector κ).prod (gaussianVector κ) := by
  have h := integral_bilin_sub_bilin_integrals_eq_gaussian_covariance_integral
    (gaussianVector κ) standard_integral_id f df g dg hf hdfc hg hdgc
    Cf Cd Cg Ce hfb hdfb hgb hdgb B
  simpa only [standard_covariance, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

end NLAlib

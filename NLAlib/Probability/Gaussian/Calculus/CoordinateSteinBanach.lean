import NLAlib.Probability.Gaussian.Calculus.Stein
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Native Banach-valued coordinate Gaussian Stein identity

The genuine scalar coordinate Stein theorem and the separating real dual
give the exact Bochner identity for any complete real normed target. The
unbounded coordinate product is handled by explicit integrability premises.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Coordinate Stein integration by parts under the actual standard product
Gaussian law, with a native Banach-valued integrand. Every term is a genuine
Bochner integral; no Gaussian covariance or derivative identity is assumed. -/
theorem integral_coordinate_smul_eq_integral_fderiv_gaussian
    (f : (κ → ℝ) → F) (hf : Differentiable ℝ f) (i : κ)
    (hfi : Integrable f (gaussianVector κ))
    (hxfi : Integrable (fun x => x i • f x) (gaussianVector κ))
    (hdfi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1)) (gaussianVector κ)) :
    (∫ x : κ → ℝ, x i • f x ∂gaussianVector κ) =
      ∫ x : κ → ℝ, fderiv ℝ f x (Pi.single i 1) ∂gaussianVector κ := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  have hd (x : κ → ℝ) : fderiv ℝ (fun y => ℓ (f y)) x=ℓ.comp (fderiv ℝ f x) :=
    (ℓ.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  have hs := integral_coordinate_mul_eq_integral_fderiv_gaussian
    (fun x => ℓ (f x)) (ℓ.differentiable.comp hf) i (ℓ.integrable_comp hfi)
    (by simpa only [map_smul,smul_eq_mul] using ℓ.integrable_comp hxfi)
    (by
      have hh := ℓ.integrable_comp hdfi
      simp_rw [hd,ContinuousLinearMap.comp_apply]
      exact hh)
  simp_rw [hd,ContinuousLinearMap.comp_apply] at hs
  rw [← ℓ.integral_comp_comm hxfi,← ℓ.integral_comp_comm hdfi]
  simpa only [map_smul,smul_eq_mul] using hs

end NLAlib

import NLAlib.Probability.Gaussian.Calculus.ComplexIntegrationByParts
import Mathlib.Algebra.BigOperators.Pi

/-!
# Bilinear contraction of the actual Gaussian Stein identity

A continuous real bilinear map contracts the full real-coordinate covariance
of a centered Gaussian vector against a bounded C¹ test. The matrix-resolvent
application may reconstruct Hermitian matrices through any real coordinates;
no covariance cancellation or interpolation identity is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {κ Ω F : Type*} [Fintype κ] [MeasurableSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem gaussian_coordinate_joint (Z : Ω → κ → ℝ)
    (hZ : HasGaussianLaw Z P) (i : κ) :
    HasGaussianLaw (fun ω => (Z ω i, Z ω)) P := by
  let L : (κ → ℝ) →L[ℝ] ℝ × (κ → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) i).prod
      (ContinuousLinearMap.id ℝ (κ → ℝ))
  simpa [L] using hZ.map_fun L

private theorem bilin_pi_expansion [DecidableEq κ]
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) (x : κ → ℝ) (y : F) :
    B x y = ∑ i, x i • B (Pi.single i 1) y := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, sum_apply, smul_apply]

/-- A continuous real bilinear map applied to a Gaussian vector and a bounded
continuous test is integrable. This proves the product integrability needed by
Gaussian Stein contraction, including singular Gaussian laws.
atlas: gaussian-integration-by-parts (partial) -/
theorem integrable_bilin_comp_of_hasGaussianLaw
    (Z : Ω → κ → ℝ) (hZ : HasGaussianLaw Z P)
    (f : (κ → ℝ) → F) (hfc : Continuous f) (C : ℝ) (hfb : ∀ x, ‖f x‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    Integrable (fun ω => B (Z ω) (f (Z ω))) P := by
  classical
  have hi (i : κ) : Integrable (fun ω => Z ω i • B (Pi.single i 1) (f (Z ω))) P := by
    have hbound (x : κ → ℝ) : ‖B (Pi.single i 1) (f x)‖ ≤ ‖B (Pi.single i 1)‖ * C :=
      ((B (Pi.single i 1)).le_opNorm (f x)).trans
        (mul_le_mul_of_nonneg_left (hfb x) (norm_nonneg _))
    exact integrable_smul_complex_comp_of_hasGaussianLaw (fun ω => Z ω i)
      (fun j ω => Z ω j) (gaussian_coordinate_joint Z hZ i)
      (fun x => B (Pi.single i 1) (f x)) ((B _).continuous.comp hfc) _ hbound
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  refine hs.congr (ae_of_all _ fun ω => ?_)
  exact (bilin_pi_expansion B (Z ω) (f (Z ω))).symm

/-- Gaussian integration by parts contracted with any continuous real bilinear
map. The full actual coordinate covariance appears on the right. The bounded
C¹ test and bounded continuous partial derivatives imply all integrability;
no matrix-specific assumption, covariance matching, or interpolation conclusion
is supplied as a hypothesis.
atlas: gaussian-integration-by-parts (partial) -/
theorem integral_bilin_eq_sum_covariance_smul_integral_of_hasGaussianLaw
    [DecidableEq κ]
    (Z : Ω → κ → ℝ) (hZ : HasGaussianLaw Z P)
    (hmean : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (f : (κ → ℝ) → F) (f' : κ → (κ → ℝ) → F)
    (hf : ∀ x, HasFDerivAt f
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight (f' j x)) x)
    (hf'c : ∀ j, Continuous (f' j)) (C C' : ℝ)
    (hfb : ∀ x, ‖f x‖ ≤ C) (hf'b : ∀ j x, ‖f' j x‖ ≤ C')
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    (∫ ω, B (Z ω) (f (Z ω)) ∂P) =
      ∑ i, ∑ j, cov[(fun ω => Z ω i), (fun ω => Z ω j); P] •
        ∫ ω, B (Pi.single i 1) (f' j (Z ω)) ∂P := by
  classical
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  let G : κ → (κ → ℝ) → ℂ := fun i x => B (Pi.single i 1) (f x)
  let G' : κ → κ → (κ → ℝ) → ℂ := fun i j x => B (Pi.single i 1) (f' j x)
  have hGc (i : κ) : Continuous (G i) := (B _).continuous.comp hfc
  have hG'c (i j : κ) : Continuous (G' i j) := (B _).continuous.comp (hf'c j)
  have hGb (i : κ) (x : κ → ℝ) : ‖G i x‖ ≤ ‖B (Pi.single i 1)‖ * C :=
    ((B (Pi.single i 1)).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_left (hfb x) (norm_nonneg _))
  have hG'b (i j : κ) (x : κ → ℝ) : ‖G' i j x‖ ≤ ‖B (Pi.single i 1)‖ * C' :=
    ((B (Pi.single i 1)).le_opNorm (f' j x)).trans
      (mul_le_mul_of_nonneg_left (hf'b j x) (norm_nonneg _))
  have hG (i : κ) (x : κ → ℝ) : HasFDerivAt (G i)
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight (G' i j x)) x := by
    have he : (B (Pi.single i 1)).comp
        (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight (f' j x)) =
        ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight (G' i j x) := by
      ext v
      simp [G', ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply, map_sum]
    have h := (B (Pi.single i 1)).hasFDerivAt.comp x (hf x)
    rw [he] at h
    exact h
  have hi (i : κ) : Integrable (fun ω => Z ω i • G i (Z ω)) P :=
    integrable_smul_complex_comp_of_hasGaussianLaw _ _ (gaussian_coordinate_joint Z hZ i)
      (G i) (hGc i) _ (hGb i)
  have hs (i : κ) : (∫ ω, Z ω i • G i (Z ω) ∂P) =
      ∑ j, cov[(fun ω => Z ω i), (fun ω => Z ω j); P] • ∫ ω, G' i j (Z ω) ∂P :=
    integral_smul_eq_sum_covariance_smul_integral_complex _ _ (gaussian_coordinate_joint Z hZ i)
      (hmean i) (G i) (G' i) (hG i) (hG'c i) _ _ (hGb i) (hG'b i)
  have he : (fun ω => B (Z ω) (f (Z ω))) =
      (fun ω => ∑ i, Z ω i • G i (Z ω)) := by
    funext ω
    exact bilin_pi_expansion B (Z ω) (f (Z ω))
  rw [he, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hs]
  rfl

end NLAlib

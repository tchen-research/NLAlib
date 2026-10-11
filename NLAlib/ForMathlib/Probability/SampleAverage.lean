import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Complex.BigOperators

/-!
# Variance of a finite sample average

Exact second moments for independent copies under a finite product law.
Source: operator re-derivation `sa:amm-variance`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- The centered squared error of an average of independent real samples is
the one-sample variance divided by the sample count. No moment hypotheses are
needed for the finite probability space.
Source: operator re-derivation `sa:amm-variance`. -/
theorem integral_centered_average_sq_pi
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (f : ι → ℝ) {c : ℕ} (hc : 0 < c) :
    ∫ ω : Fin c → ι, ((1 / (c : ℝ)) * ∑ j, f (ω j) - ∫ i, f i ∂ν) ^ 2
      ∂Measure.pi (fun _ => ν) =
      (1 / (c : ℝ)) * (∫ i, f i ^ 2 ∂ν - (∫ i, f i ∂ν) ^ 2) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hL : MemLp f 2 ν :=
    (memLp_two_iff_integrable_sq (AEStronglyMeasurable.of_discrete)).mpr .of_finite
  let X : (Fin c → ι) → ℝ := fun ω => (1 / (c : ℝ)) * ∑ j, f (ω j)
  have hmean : ∫ ω, X ω ∂Measure.pi (fun _ : Fin c => ν) = ∫ i, f i ∂ν := by
    dsimp only [X]
    rw [integral_const_mul, integral_finsetSum _ (fun _ _ => .of_finite)]
    have heval : ∀ j : Fin c,
        ∫ ω, f (ω j) ∂Measure.pi (fun _ : Fin c => ν) = ∫ i, f i ∂ν := by
      intro j
      exact integral_comp_eval (show AEStronglyMeasurable f ν from .of_discrete)
    simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : variance X (Measure.pi (fun _ : Fin c => ν)) =
      (1 / (c : ℝ)) * (∫ i, f i ^ 2 ∂ν - (∫ i, f i ∂ν) ^ 2) := by
    dsimp only [X]
    rw [variance_const_mul]
    have hsum := variance_sum_pi (fun _ : Fin c => hL)
    have hfun : (∑ j : Fin c, (fun ω : Fin c → ι => f (ω j))) =
        (fun ω : Fin c → ι => ∑ j, f (ω j)) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hfun] at hsum
    rw [hsum, variance_eq_sub hL]
    simp only [Pi.pow_apply]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [variance_eq_integral (show AEMeasurable X _ from Measurable.of_discrete.aemeasurable),
    hmean] at hvar
  exact hvar

/-- The squared complex absolute error of an independent sample average is
the complex one-sample variance divided by the sample count. Source:
operator re-derivation `sa:amm-variance`, by real and imaginary variances. -/
theorem integral_centered_average_norm_sq_pi
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (f : ι → ℂ) {c : ℕ} (hc : 0 < c) :
    ∫ ω : Fin c → ι, ‖(1 / (c : ℝ)) • ∑ j, f (ω j) - ∫ i, f i ∂ν‖ ^ 2
      ∂Measure.pi (fun _ => ν) =
      (1 / (c : ℝ)) * (∫ i, ‖f i‖ ^ 2 ∂ν - ‖∫ i, f i ∂ν‖ ^ 2) := by
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hr := integral_centered_average_sq_pi ν (fun i => (f i).re) hc
  have hi := integral_centered_average_sq_pi ν (fun i => (f i).im) hc
  simp_rw [hnorm, Complex.sub_re, Complex.sub_im, Complex.smul_re,
    Complex.smul_im, Complex.re_sum, Complex.im_sum, smul_eq_mul]
  rw [integral_add .of_finite .of_finite, integral_add .of_finite .of_finite]
  have hre : (∫ i, f i ∂ν).re = ∫ i, (f i).re ∂ν := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (show Integrable f ν from .of_finite)).symm
  have him : (∫ i, f i ∂ν).im = ∫ i, (f i).im ∂ν := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im (show Integrable f ν from .of_finite)).symm
  rw [hre, him, hr, hi]
  ring

end NLAlib

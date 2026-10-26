import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A uniform scalar Gaussian lower tail

Integrating the Gaussian density on the unit interval beginning at a
nonnegative threshold gives a uniform exponential lower tail. This
elementary estimate supplies lower Gaussian maxima and the tail-comparison
step in Latała--van Handel--Youssef, arXiv:1711.00807v2, Corollary 1.4.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

/-- The mass of a unit interval beginning at a nonnegative threshold has
a dimension-free lower bound obtained from the actual Gaussian density. -/
theorem exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_unit_interval
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2) ≤
      (gaussianReal 0 1).real (Icc t (t + 1)) := by
  have hpoint (x : ℝ) (hx : x ∈ Icc t (t + 1)) :
      Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2) ≤
        gaussianPDFReal 0 1 x := by
    have hx0 : 0 ≤ x := ht.trans hx.1
    have hsq : x ^ 2 ≤ (t + 1) ^ 2 := pow_le_pow_left₀ hx0 hx.2 2
    have he : -t ^ 2 - 1 ≤ -x ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
    have hexp := Real.exp_le_exp.mpr he
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2) =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-t ^ 2 - 1) by
        rw [sub_eq_add_neg, Real.exp_add]; ring]
    simpa only [one_div] using mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))
  have hconst : IntegrableOn
      (fun _ : ℝ => Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2))
      (Icc t (t + 1)) volume := integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hmono := setIntegral_mono_on hconst (integrable_gaussianPDFReal 0 1).restrict
    measurableSet_Icc hpoint
  rw [integral_const] at hmono
  simp only [Measure.real, Measure.restrict_apply_univ] at hmono
  change volume.real (Icc t (t + 1)) • _ ≤ _ at hmono
  rw [Real.volume_real_Icc_of_le (by linarith),
    show t + 1 - t = 1 by ring, one_smul] at hmono
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num), ENNReal.toReal_ofReal
    (integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x)]
  exact hmono

/-- A scalar standard Gaussian has a uniform lower absolute tail. The
positive constant is explicit and the event includes its threshold. -/
theorem exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2) ≤
      (gaussianReal 0 1).real {x : ℝ | t ≤ |x|} := by
  apply (exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_unit_interval t ht).trans
  exact measureReal_mono (fun x hx => hx.1.trans (le_abs_self x)) (by finiteness)

end NLAlib

import NLAlib.ForMathlib.Analysis.Complex.Harmonic.HerglotzRepresentation
import NLAlib.ForMathlib.Analysis.Complex.CayleyTransform

/-!
# Positive-imaginary holomorphic functions in Cayley coordinates

Transport the proved disk Herglotz representation to the upper half plane.
The positive measure still lives on the compact circle; finite real-line
Stieltjes mass requires the additional asymptotic normalization.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1,
arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Metric Set

namespace Complex

/-- A positive-imaginary holomorphic upper-half-plane function has an
actual positive finite representing circle measure in Cayley coordinates.
Its mass is `Im f(i)`. This compact form requires no asymptotic hypothesis.
Source: the Herglotz bridge in Ajanki--Erdos--Kruger (2019), Proposition 2.1.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem _root_.AnalyticOnNhd.exists_finiteMeasure_cayley_integral_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im) :
    ∃ μ : FiniteMeasure Circle, (μ.mass : ℝ) = (f I).im ∧
      ∀ z : ℂ, 0 < z.im → f z = ((f I).re : ℂ) +
        I * ∫ ξ : Circle, herglotzRieszKernel 0 (cayleyTransform z) ξ ∂(μ : Measure Circle) := by
  let F : ℂ → ℂ := fun w => -I * f (inverseCayleyTransform w)
  have him (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      0 < (inverseCayleyTransform w).im :=
    im_inverseCayleyTransform_pos (by simpa only [mem_ball, dist_zero_right] using hw)
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    intro w hw
    exact analyticAt_const.mul ((hf _ (him w hw)).comp
      (analyticOnNhd_inverseCayleyTransform w hw))
  have hFpos (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : 0 ≤ (F w).re := by
    simpa [F] using hpos _ (him w hw)
  obtain ⟨μ, hmass, hμ⟩ := hF.exists_finiteMeasure_herglotzRieszKernel_eq hFpos
  have hmass' : (μ.mass : ℝ) = (f I).im := by
    simpa [F] using hmass
  refine ⟨μ, hmass', ?_⟩
  intro z hz
  have hw : cayleyTransform z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right] using norm_cayleyTransform_lt_one hz
  have he := hμ (cayleyTransform z) hw
  simp only [F, inverseCayleyTransform_cayleyTransform (add_I_ne_zero_of_im_pos hz),
    inverseCayleyTransform_zero, mul_im, neg_im, I_re, I_im,
    zero_mul, zero_add, neg_mul, one_mul] at he
  have hm := congrArg (fun a : ℂ => I * a) he
  simp only [mul_add, ← mul_assoc, I_mul_I, mul_neg, neg_neg, neg_one_mul,
    Complex.ofReal_neg] at hm
  exact hm

end Complex

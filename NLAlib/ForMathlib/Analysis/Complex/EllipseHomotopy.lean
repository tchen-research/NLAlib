import NLAlib.ForMathlib.Analysis.Complex.FreeLoopHomotopy
import NLAlib.ForMathlib.Analysis.Complex.ThinEllipsePositivity
import NLAlib.ForMathlib.MeasureTheory.CirclePath

/-!
# Smooth deformation from an exterior circle to thin ellipses

The real semiaxis remains fixed, while the imaginary semiaxis decreases through
positive values. Points of the homotopy either lie off the real axis or are the
fixed exterior endpoints. Native smooth path integration therefore identifies
the circle integral with each ellipse integral, using actual local primitives.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped unitInterval Topology

namespace Complex

/-- The standard ellipse as a native closed path on the unit interval. -/
def ellipsePath (M ε : ℝ) : Path (M : ℂ) (M : ℂ) :=
  Path.ofLine (f := fun t : ℝ => ellipseMap M ε (2 * Real.pi * t))
    (by unfold ellipseMap; fun_prop)
    (by simp [ellipseMap]) (by simp [ellipseMap])

/-- The ellipse path agrees with its angular parametrization through angle
`2πt` on the full closed unit interval. -/
theorem ellipsePath_extend_apply {M ε t : ℝ} (ht : t ∈ I) :
    (ellipsePath M ε).extend t = ellipseMap M ε (2 * Real.pi * t) := by
  rw [Path.extend_apply _ ht]
  rfl

private theorem contDiff_ellipse_param (M ε : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => ellipseMap M ε (2 * Real.pi * t)) := by
  have hr : ContDiff ℝ 1 (fun t : ℝ => M * Real.cos (2 * Real.pi * t)) := by fun_prop
  have hi : ContDiff ℝ 1 (fun t : ℝ => ε * Real.sin (2 * Real.pi * t)) := by fun_prop
  simpa only [ellipseMap, ofRealCLM_apply, Pi.add_apply, Function.comp_def] using!
    (ofRealCLM.contDiff.comp hr).add ((ofRealCLM.contDiff.comp hi).mul contDiff_const)

/-- Native ellipse paths are continuously differentiable at both endpoints. -/
theorem contDiffOn_ellipsePath_extend (M ε : ℝ) :
    ContDiffOn ℝ 1 (ellipsePath M ε).extend I := by
  have h := contDiff_ellipse_param M ε
  exact h.contDiffOn.congr (fun t ht => ellipsePath_extend_apply ht)

/-- The native ellipse path integral is its angular ellipse integral, with
counterclockwise orientation and no change in its normalization. -/
theorem curveIntegral_ellipsePath_eq_ellipseIntegral (f : ℂ → ℂ) (M ε : ℝ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) (ellipsePath M ε) =
      ellipseIntegral f M ε := by
  have hγ := contDiff_ellipse_param M ε
  unfold ellipsePath
  rw [Path.curveIntegral_ofLine_eq_intervalIntegral hγ]
  have hd (t : ℝ) : deriv (fun t : ℝ => ellipseMap M ε (2 * Real.pi * t)) t =
      (2 * Real.pi) • deriv (ellipseMap M ε) (2 * Real.pi * t) := by
    simpa only [Function.comp_def, mul_one, (hasDerivAt_ellipseMap _ _ _).deriv] using!
      ((hasDerivAt_ellipseMap M ε (2 * Real.pi * t)).scomp t
        ((hasDerivAt_id t).const_mul (2 * Real.pi))).deriv
  simp_rw [hd, smul_mul_assoc]
  rw [intervalIntegral.integral_smul]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun θ : ℝ => deriv (ellipseMap M ε) θ * f (ellipseMap M ε θ)) (2 * Real.pi)
    (a := (0 : ℝ)) (b := 1)
  simpa only [mul_zero, mul_one, ellipseIntegral, smul_eq_mul] using hs

private theorem ellipseMap_self (M θ : ℝ) : ellipseMap M M θ = circleMap 0 M θ := by
  apply Complex.ext <;>
    simp only [ellipseMap, circleMap, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, mul_one, zero_add, add_zero,
      sub_zero, exp_re, exp_im, Real.exp_zero, one_mul]

/-- Every point of a nondegenerate ellipse with real semiaxis outside a disk
is either nonreal or outside that disk. Thus its flattening avoids every branch
cut contained in the smaller real segment. -/
theorem ellipseMap_mem_off_real_or_exterior {M ε R θ : ℝ}
    (hM : 0 < M) (hε : 0 < ε) (hRM : R < M) :
    (ellipseMap M ε θ).im ≠ 0 ∨ R < ‖ellipseMap M ε θ‖ := by
  by_cases hs : Real.sin θ = 0
  · right
    have hn : ‖ellipseMap M ε θ‖ = M := by
      rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
        simp only [ellipseMap, hs, hc, mul_one, mul_neg, mul_zero, ofReal_zero,
          zero_mul, add_zero, ofReal_neg, norm_neg, norm_real, Real.norm_eq_abs,
          abs_of_pos hM]
    rwa [hn]
  · left
    simpa only [ellipseMap, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using mul_ne_zero hε.ne' hs

/-- A circle of radius `M` deforms through smooth ellipses to any positive
vertical semiaxis inside the union of the nonreal plane and the exterior of a
smaller disk. Holomorphy on that actual domain identifies the contour integrals.
No real-axis boundary values inside the disk are assumed. -/
theorem circleIntegral_eq_ellipseIntegral_of_differentiableOn_off_real_or_exterior
    {f : ℂ → ℂ} {R M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (hRM : R < M)
    (hf : DifferentiableOn ℂ f {z | z.im ≠ 0 ∨ R < ‖z‖}) :
    (∮ z in C(0, M), f z) = ellipseIntegral f M ε := by
  let ψ : ℝ × ℝ → ℂ := fun p =>
    ellipseMap M ((1 - p.1) * M + p.1 * ε) (2 * Real.pi * p.2)
  have hψ : Continuous ψ := by unfold ψ ellipseMap; fun_prop
  have hΩ : IsOpen {z : ℂ | z.im ≠ 0 ∨ R < ‖z‖} :=
    (isOpen_ne_fun continuous_im continuous_const).union
      (isOpen_lt continuous_const continuous_norm)
  have hm (p : ℝ × ℝ) (hp : p ∈ Icc (0 : ℝ × ℝ) 1) :
      0 < (1 - p.1) * M + p.1 * ε := by
    have ht0 : 0 ≤ p.1 := hp.1.1
    have ht1 : p.1 ≤ 1 := hp.2.1
    by_cases ht : p.1 = 1
    · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using hε
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hM)
        (mul_nonneg ht0 hε.le)
  have hc := curveIntegral_eq_of_differentiableOn_of_freeHomotopy
    (circlePath 0 M) (ellipsePath M ε) hψ hΩ hf
    (fun p hp => ellipseMap_mem_off_real_or_exterior hM (hm p hp) hRM)
    (fun t ht => by rw [circlePath_extend_apply ht]; simp only [ψ, sub_zero, one_mul,
      zero_mul, add_zero]; exact (ellipseMap_self M _).symm)
    (fun t ht => by rw [ellipsePath_extend_apply ht]; simp only [ψ, sub_self, zero_mul,
      one_mul, zero_add])
    (fun t _ => by simp [ψ, ellipseMap])
    (contDiffOn_circlePath_extend 0 M) (contDiffOn_ellipsePath_extend M ε)
  rwa [curveIntegral_circlePath_eq_circleIntegral, curveIntegral_ellipsePath_eq_ellipseIntegral] at hc

end Complex

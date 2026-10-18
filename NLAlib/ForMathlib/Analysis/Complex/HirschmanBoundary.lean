import NLAlib.ForMathlib.Analysis.Complex.HirschmanConformal
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Exact boundary parametrization for weighted strip interpolation

An arctangent parametrization transports normalized circle angle to the actual
Cauchy law on the real boundary of the upper half-plane. Exponential boundary
coordinates then give the displayed Stein--Hirschman strip densities.
-/

noncomputable section

open Real Set Metric MeasureTheory

namespace Complex

/-- A bijective angle parametrization of the circle with the point `1` removed. -/
def hirschmanBoundaryAngle (q : ℝ) : ℝ := π + 2 * arctan q

theorem hirschmanBoundaryAngle_mem (q : ℝ) :
    hirschmanBoundaryAngle q ∈ Ioo (0 : ℝ) (2 * π) := by
  dsimp [hirschmanBoundaryAngle]
  constructor <;> linarith [arctan_mem_Ioo q |>.1, arctan_mem_Ioo q |>.2]

theorem strictMono_hirschmanBoundaryAngle : StrictMono hirschmanBoundaryAngle := by
  intro x y hxy
  dsimp [hirschmanBoundaryAngle]
  linarith [arctan_strictMono hxy]

theorem range_hirschmanBoundaryAngle : Set.range hirschmanBoundaryAngle = Ioo (0 : ℝ) (2 * π) := by
  ext θ
  constructor
  · rintro ⟨q, rfl⟩
    exact hirschmanBoundaryAngle_mem q
  · intro hθ
    refine ⟨Real.tan ((θ - π) / 2), ?_⟩
    unfold hirschmanBoundaryAngle
    rw [Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
    ring

theorem hasDerivAt_hirschmanBoundaryAngle (q : ℝ) :
    HasDerivAt hirschmanBoundaryAngle (2 / (1 + q ^ 2)) q := by
  have h := ((Real.hasDerivAt_arctan q).const_mul 2).const_add π
  change HasDerivAt hirschmanBoundaryAngle (2 * (1 / (1 + q ^ 2))) q at h
  exact h.congr_deriv (by ring)

/-- The rational and trigonometric parametrizations are exactly equal. -/
theorem circleMap_hirschmanBoundaryAngle (q : ℝ) :
    circleMap 0 1 (hirschmanBoundaryAngle q) = ((q : ℂ) - I) / ((q : ℂ) + I) := by
  have hcos : Real.cos (π + 2 * arctan q) = (q ^ 2 - 1) / (1 + q ^ 2) := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, zero_mul, sub_zero, neg_one_mul,
      Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp
    ring
  have hsin : Real.sin (π + 2 * arctan q) = -2 * q / (1 + q ^ 2) := by
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, zero_add, neg_one_mul,
      Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hs : sqrt (1 + q ^ 2) ≠ 0 := ne_of_gt (sqrt_pos.2 (by positivity))
    field_simp
    rw [sq_sqrt (by positivity)]
  apply Complex.ext
  · simp only [circleMap, zero_add, ofReal_one, one_mul, hirschmanBoundaryAngle,
      mul_I_re, mul_I_im, ofReal_im, ofReal_re, Complex.exp_re, neg_zero,
      zero_sub, Real.exp_zero, one_mul, div_re, sub_re, add_re, I_re, sub_zero,
      add_zero, sub_im, add_im, I_im, zero_sub, zero_add, normSq_apply]
    rw [hcos]
    ring
  · simp only [circleMap, zero_add, ofReal_one, one_mul, hirschmanBoundaryAngle,
      mul_I_re, mul_I_im, ofReal_im, ofReal_re, Complex.exp_im, neg_zero,
      zero_sub, Real.exp_zero, one_mul, div_im, sub_re, add_re, I_re, sub_zero,
      add_zero, sub_im, add_im, I_im, zero_sub, zero_add, normSq_apply]
    rw [hsin]
    ring

/-- In these boundary coordinates the prescribed half-plane map is simply affine. -/
theorem hirschmanDiskToHalfPlane_circleMap_boundary (a b q : ℝ) :
    hirschmanDiskToHalfPlane a b (circleMap 0 1 (hirschmanBoundaryAngle q)) = ((a + b * q : ℝ) : ℂ) := by
  rw [circleMap_hirschmanBoundaryAngle]
  have hden : (q : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hne : ((q : ℂ) - I) / ((q : ℂ) + I) ≠ 1 := by
    intro h
    have he := (div_eq_one_iff_eq hden).mp h
    have := congrArg Complex.im he
    norm_num at this
  have hquot : (1 + ((q : ℂ) - I) / ((q : ℂ) + I)) /
      (1 - ((q : ℂ) - I) / ((q : ℂ) + I)) = -(q : ℂ) * I := by
    field_simp
    ring_nf
    simp [I_sq]
  unfold hirschmanDiskToHalfPlane
  rw [hquot]
  push_cast
  ring_nf
  simp [I_sq]

/-- The actual boundary circle average is exactly the arctangent parametrized
integral with the standard Cauchy density. -/
theorem circleAverage_eq_integral_hirschmanBoundaryAngle (F : ℂ → ℝ) :
    Real.circleAverage F 0 1 =
      ∫ q : ℝ, (1 / (π * (1 + q ^ 2))) * F (circleMap 0 1 (hirschmanBoundaryAngle q)) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun q _ => (hasDerivAt_hirschmanBoundaryAngle q).hasDerivWithinAt)
    strictMono_hirschmanBoundaryAngle.injective.injOn
    (fun θ => F (circleMap 0 1 θ))
  rw [image_univ, range_hirschmanBoundaryAngle] at hchange
  rw [Real.circleAverage, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, hchange]
  simp only [Measure.restrict_univ, smul_eq_mul]
  have habs (q : ℝ) : |2 / (1 + q ^ 2)| = 2 / (1 + q ^ 2) := abs_of_pos (by positivity)
  simp_rw [habs]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    field_simp

/-- The actual boundary circle average transports to the standard Cauchy
density and affine upper-half-plane boundary coordinates. -/
theorem circleAverage_hirschmanDiskToHalfPlane (a b : ℝ) (F : ℂ → ℝ) :
    Real.circleAverage (fun z => F (hirschmanDiskToHalfPlane a b z)) 0 1 =
      ∫ q : ℝ, (1 / (π * (1 + q ^ 2))) * F ((a + b * q : ℝ) : ℂ) := by
  rw [circleAverage_eq_integral_hirschmanBoundaryAngle]
  simp_rw [hirschmanDiskToHalfPlane_circleMap_boundary]

/-- The circle boundary pushforward is the actual location-scale Cauchy
density on the real line, not an unspecified boundary distribution. -/
theorem circleAverage_hirschmanDiskToHalfPlane_eq_cauchy (a : ℝ) {b : ℝ} (hb : 0 < b)
    (F : ℂ → ℝ) :
    Real.circleAverage (fun z => F (hirschmanDiskToHalfPlane a b z)) 0 1 =
      ∫ w : ℝ, ProbabilityTheory.cauchyPDFReal a (⟨b, hb.le⟩ : NNReal) w * F (w : ℂ) := by
  have hRange : (fun q : ℝ => a + b * q) '' Set.univ = Set.univ := by
    ext w
    constructor
    · exact fun _ => Set.mem_univ _
    · intro _
      refine ⟨(w - a) / b, Set.mem_univ _, ?_⟩
      field_simp
      ring
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun q _ => (((hasDerivAt_id q).const_mul b).const_add a).hasDerivWithinAt)
    (show Set.InjOn (fun q : ℝ => a + b * q) Set.univ from fun q _ w _ h => by
      have := (add_left_cancel h : b * q = b * w)
      exact mul_left_cancel₀ (ne_of_gt hb) this)
    (fun w : ℝ => ProbabilityTheory.cauchyPDFReal a (⟨b, hb.le⟩ : NNReal) w * F (w : ℂ))
  simp only [id_eq, mul_one] at hchange
  rw [hRange, Measure.restrict_univ] at hchange
  rw [circleAverage_hirschmanDiskToHalfPlane, hchange]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    simp only [abs_of_pos hb, smul_eq_mul, ProbabilityTheory.cauchyPDFReal]
    change 1 / (π * (1 + q ^ 2)) * F ((a + b * q : ℝ) : ℂ) =
      b * (π⁻¹ * b * ((a + b * q - a) ^ 2 + b ^ 2)⁻¹ * F ((a + b * q : ℝ) : ℂ))
    have hd : b * (π⁻¹ * b * ((a + b * q - a) ^ 2 + b ^ 2)⁻¹) =
        1 / (π * (1 + q ^ 2)) := by
      field_simp
      ring
    rw [← mul_assoc, hd]

end Complex

import NLAlib.ForMathlib.MeasureTheory.CircleProbability
import NLAlib.ForMathlib.MeasureTheory.CompactLaplaceLimit
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Positive harmonic functions represented by finite circle measures

The positive measures are constructed from the radial boundary densities.
The native Poisson formula and compactness of finite measures give one
representing measure for all points in the disk. No boundary limits or
representing-measure assumption is required.
Source: the scalar Herglotz representation used in Ajanki--Erdos--Kruger
(2019), Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set Metric Complex Real InnerProductSpace
open scoped Topology NNReal

namespace Complex

/-- The native Poisson kernel is a continuous test on the unit circle
when its pole lies strictly inside the disk. -/
theorem continuous_poissonKernel_circle {w : ℂ} (hw : w ∈ ball 0 1) :
    Continuous (fun ξ : Circle => poissonKernel 0 w ξ) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  have hcoe : Continuous (fun ξ : Circle => (ξ : ℂ)) := continuous_subtype_val
  have hc : Continuous (fun ξ : Circle => herglotzRieszKernel 0 w ξ) :=
    (continuousOn_herglotzRieszKernel_sphere hw).comp_continuous
      hcoe (by
        intro ξ
        simpa only [mem_sphere, dist_zero_right, abs_one] using Circle.norm_coe ξ)
  exact Complex.continuous_re.comp hc

/-- Scaling both the boundary point and the pole by a nonzero real
number leaves the Poisson kernel unchanged. -/
theorem poissonKernel_zero_mul_real (r : ℝ) (hr : r ≠ 0) (w ξ : ℂ) :
    poissonKernel 0 ((r : ℂ) * w) ((r : ℂ) * ξ) = poissonKernel 0 w ξ := by
  simp only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def, sub_zero]
  congr 1
  rw [← mul_add, ← mul_sub, mul_div_mul_left _ _ (by exact_mod_cast hr)]

end Complex

namespace InnerProductSpace

private theorem radial_poisson_representation {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ μ : FiniteMeasure Circle, (μ.mass : ℝ) = u 0 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        (∫ ξ : Circle, poissonKernel 0 w ξ ∂(μ : Measure Circle)) = u ((r : ℂ) * w) := by
  have hradius (ξ : Circle) : (r : ℂ) * ξ ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Circle.norm_coe, mul_one] using hr1
  have hcont : Continuous (fun ξ : Circle => u ((r : ℂ) * ξ)) :=
    hu.continuousOn.comp_continuous (by fun_prop) hradius
  have hnonneg (ξ : Circle) : 0 ≤ u ((r : ℂ) * ξ) := hpos _ (hradius ξ)
  let ν := Circle.probabilityMeasure.withDensity (fun ξ : Circle => ENNReal.ofReal (u ((r : ℂ) * ξ)))
  have hint : Integrable (fun ξ : Circle => u ((r : ℂ) * ξ)) Circle.probabilityMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  let μ : FiniteMeasure Circle := ⟨ν, inferInstance⟩
  have hintegral (f : Circle → ℝ) : (∫ ξ, f ξ ∂(μ : Measure Circle)) =
      ∫ ξ, u ((r : ℂ) * ξ) * f ξ ∂Circle.probabilityMeasure := by
    change (∫ ξ, f ξ ∂ν) = _
    dsimp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul hcont.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]
  have hmass : (μ.mass : ℝ) = u 0 := by
    have hm := (show HarmonicOnNhd u (closedBall 0 |r|) from
      by simpa only [abs_of_pos hr] using hu.mono (closedBall_subset_ball hr1)).circleAverage_eq
    have hi := hintegral (fun _ => 1)
    simp only [mul_one] at hi
    have hi' := Circle.integral_probabilityMeasure_eq_circleAverage
      (fun ξ : ℂ => u ((r : ℂ) * ξ))
    have he : Real.circleAverage (fun ξ : ℂ => u ((r : ℂ) * ξ)) 0 1 = Real.circleAverage u 0 r := by
      simpa only [add_zero] using (Real.circleAverage_eq_circleAverage_zero_one (f := u) (c := 0) (R := r)).symm
    have hall := hi.trans (hi'.trans (he.trans hm))
    change (ν.real univ) = u 0
    simpa only [μ, FiniteMeasure.toMeasure_mk, integral_const, smul_eq_mul, mul_one] using hall
  refine ⟨μ, hmass, ?_⟩
  intro w hw
  have hrw : (r : ℂ) * w ∈ ball (0 : ℂ) r := by
    simp only [mem_ball, dist_zero_right] at hw ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hp := (hu.mono (closedBall_subset_ball hr1)).circleAverage_poissonKernel_smul hrw
  rw [hintegral]
  have he : Real.circleAverage
      (fun ξ : ℂ => u ((r : ℂ) * ξ) * poissonKernel 0 w ξ) 0 1 =
      Real.circleAverage (poissonKernel 0 ((r : ℂ) * w) • u) 0 r := by
    rw [Real.circleAverage_eq_circleAverage_zero_one
      (f := poissonKernel 0 ((r : ℂ) * w) • u) (c := 0) (R := r)]
    apply Real.circleAverage_congr_sphere
    intro ξ _
    change u ((r : ℂ) * ξ) * poissonKernel 0 w ξ =
      poissonKernel 0 ((r : ℂ) * w) ((r : ℂ) * ξ + 0) * u ((r : ℂ) * ξ + 0)
    rw [add_zero, poissonKernel_zero_mul_real r hr.ne']
    exact mul_comm _ _
  exact (Circle.integral_probabilityMeasure_eq_circleAverage
    (fun ξ : ℂ => u ((r : ℂ) * ξ) * poissonKernel 0 w ξ)).trans (he.trans hp)

/-- Every nonnegative harmonic function on the open unit disk is the
Poisson integral of an actual positive finite unit-circle measure, of mass
equal to its value at the center. Boundary regularity is not assumed.
Source: the scalar Herglotz theorem used by Ajanki--Erdos--Kruger (2019),
Proposition 2.1, arXiv:1604.08188v5.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem HarmonicOnNhd.exists_finiteMeasure_poissonKernel_eq {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z) :
    ∃ μ : FiniteMeasure Circle, (μ.mass : ℝ) = u 0 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        (∫ ξ : Circle, poissonKernel 0 w ξ ∂(μ : Measure Circle)) = u w := by
  let K : ball (0 : ℂ) 1 → C(Circle, ℝ) := fun w =>
    ⟨fun ξ => poissonKernel 0 w ξ, continuous_poissonKernel_circle w.property⟩
  let C : NNReal := ⟨u 0, hpos 0 (by simp)⟩
  let F : ℝ → ball (0 : ℂ) 1 → ℝ := fun r w => u ((r : ℂ) * w)
  have hrep : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∃ μ : FiniteMeasure Circle,
      μ.mass ≤ C ∧ ∀ w, (∫ ξ, K w ξ ∂(μ : Measure Circle)) = F r w := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    obtain ⟨μ, hmass, hμ⟩ := radial_poisson_representation hu hpos hr.1 hr.2
    refine ⟨μ, ?_, fun w => hμ w w.property⟩
    change (μ.mass : ℝ) ≤ u 0
    exact hmass.le
  have hlim (w : ball (0 : ℂ) 1) : Tendsto (fun r => F r w) (𝓝[<] (1 : ℝ)) (𝓝 (u w)) := by
    have hmul : Continuous (fun r : ℝ => (r : ℂ) * (w : ℂ)) := by fun_prop
    have ht : Tendsto (fun r : ℝ => (r : ℂ) * (w : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (w : ℂ)) := by
      simpa only [ofReal_one, one_mul] using
        (hmul.continuousAt (x := 1)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    exact (hu w w.property).1.continuousAt.tendsto.comp ht
  obtain ⟨μ, _, hμ⟩ := NLAlib.exists_finiteMeasure_integral_eq_of_tendsto
    K C F (fun w => u w) hrep hlim
  refine ⟨μ, ?_, fun w hw => hμ ⟨w, hw⟩⟩
  have hm := hμ ⟨0, by simp⟩
  change (∫ ξ : Circle, poissonKernel 0 0 ξ ∂(μ : Measure Circle)) = u 0 at hm
  change ((μ : Measure Circle).real univ) = u 0
  simpa only [poissonKernel_def, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, Circle.norm_coe, one_pow, div_one, integral_const, smul_eq_mul, mul_one] using hm

end InnerProductSpace

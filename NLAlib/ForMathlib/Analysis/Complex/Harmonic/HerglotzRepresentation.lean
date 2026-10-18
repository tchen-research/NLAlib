import NLAlib.ForMathlib.Analysis.Complex.Harmonic.PositiveRepresentation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The scalar disk Herglotz representation

A holomorphic function with nonnegative real part is represented by an actual
positive finite unit-circle measure and its imaginary value at the center.
The positive harmonic measure is constructed by radial approximation, and
the complex integral is differentiated with a proved compact uniform bound.
Source: the scalar Herglotz theorem used by Ajanki--Erdos--Kruger (2019),
Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set Metric Complex InnerProductSpace
open scoped Topology

namespace Complex

/-- A unit-circle point differs from every point inside the open unit disk. -/
theorem circle_coe_sub_ne_zero {w : ℂ} (hw : w ∈ ball 0 1) (ξ : Circle) :
    (ξ : ℂ) - w ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [Circle.norm_coe] at he
  have hh : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  linarith

/-- The complex Herglotz kernel is continuous on the actual unit circle. -/
theorem continuous_herglotzRieszKernel_circle {w : ℂ} (hw : w ∈ ball 0 1) :
    Continuous (fun ξ : Circle => herglotzRieszKernel 0 w ξ) := by
  simp only [herglotzRieszKernel_def, sub_zero]
  exact (continuous_subtype_val.add continuous_const).div
    (continuous_subtype_val.sub continuous_const) (circle_coe_sub_ne_zero hw)

/-- Differentiation of the Herglotz kernel in its interior pole. -/
theorem hasDerivAt_herglotzRieszKernel_pole {w : ℂ} (hw : w ∈ ball 0 1) (ξ : Circle) :
    HasDerivAt (fun z => herglotzRieszKernel 0 z ξ)
      (2 * (ξ : ℂ) / ((ξ : ℂ) - w) ^ 2) w := by
  have h := ((hasDerivAt_const w (ξ : ℂ)).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w (ξ : ℂ)).sub (hasDerivAt_id w)) (circle_coe_sub_ne_zero hw ξ)
  have h' : HasDerivAt (fun z : ℂ => ((ξ : ℂ) + z) / ((ξ : ℂ) - z))
      (((ξ : ℂ) - w + ((ξ : ℂ) + w)) / ((ξ : ℂ) - w) ^ 2) w := by
    convert! h using 1
    simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add,
      zero_sub, one_mul, mul_neg_one, sub_neg_eq_add]
  have he : (ξ : ℂ) - w + ((ξ : ℂ) + w) = 2 * (ξ : ℂ) := by ring
  simpa only [herglotzRieszKernel_def, sub_zero, he] using h'

/-- The actual Herglotz integral of any positive finite circle measure is
complex differentiable at each point of the disk. A compact neighborhood
constructs the common domination bound required under the integral. -/
theorem hasDerivAt_integral_herglotzRieszKernel (μ : Measure Circle) [IsFiniteMeasure μ]
    {w : ℂ} (hw : w ∈ ball 0 1) :
    HasDerivAt (fun z => ∫ ξ : Circle, herglotzRieszKernel 0 z ξ ∂μ)
      (∫ ξ : Circle, 2 * (ξ : ℂ) / ((ξ : ℂ) - w) ^ 2 ∂μ) w := by
  let r := (1 - ‖w‖) / 2
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have hr : 0 < r := by dsimp [r]; linarith
  have hinside (z : ℂ) (hz : z ∈ closedBall w r) : z ∈ ball (0 : ℂ) 1 := by
    have hdist : ‖z - w‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hn := norm_add_le (z - w) w
    rw [sub_add_cancel] at hn
    simp only [mem_ball, dist_zero_right]
    dsimp [r] at hdist
    linarith
  let D : ℂ → Circle → ℂ := fun z ξ => 2 * (ξ : ℂ) / ((ξ : ℂ) - z) ^ 2
  have hD : ContinuousOn (fun p : ℂ × Circle => D p.1 p.2) (closedBall w r ×ˢ univ) := by
    dsimp [D]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact pow_ne_zero 2 (circle_coe_sub_ne_zero (hinside p.1 hp.1) p.2)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall w r).prod isCompact_univ).bddAbove_image hD.norm
  have hcontD : Continuous (D w) := by
    dsimp [D]
    exact (continuous_const.mul continuous_subtype_val).div
      ((continuous_subtype_val.sub continuous_const).pow 2)
      (fun ξ => pow_ne_zero 2 (circle_coe_sub_ne_zero hw ξ))
  have hi : Integrable (fun ξ : Circle => herglotzRieszKernel 0 w ξ) μ :=
    (continuous_herglotzRieszKernel_circle hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := closedBall w r) (bound := fun _ => B) (closedBall_mem_nhds _ hr)
    (F := fun z ξ => herglotzRieszKernel 0 z ξ) (F' := D)
    (by
      filter_upwards [closedBall_mem_nhds w hr] with z hz
      exact (continuous_herglotzRieszKernel_circle (hinside z hz)).aestronglyMeasurable)
    hi hcontD.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ z hz => hB ⟨(z, ξ), ⟨hz, mem_univ _⟩, rfl⟩))
    (integrable_const B)
    (Filter.Eventually.of_forall (fun ξ z hz => hasDerivAt_herglotzRieszKernel_pole (hinside z hz) ξ))
  exact h.2

/-- A holomorphic function with nonnegative real part on the unit disk
has an actual positive finite Herglotz representing measure. The measure's
mass is the real value at the center and the imaginary additive constant
is the imaginary value there. No boundary regularity is required.
Source: the scalar Herglotz theorem used by Ajanki--Erdos--Kruger (2019),
Proposition 2.1, arXiv:1604.08188v5.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem _root_.AnalyticOnNhd.exists_finiteMeasure_herglotzRieszKernel_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hpos : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re) :
    ∃ μ : FiniteMeasure Circle, (μ.mass : ℝ) = (f 0).re ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        f w = Complex.I * (f 0).im +
          ∫ ξ : Circle, herglotzRieszKernel 0 w ξ ∂(μ : Measure Circle) := by
  have hu : HarmonicOnNhd (fun w => (f w).re) (ball 0 1) :=
    fun w hw => (hf w hw).harmonicAt_re
  obtain ⟨μ, hmass, hμ⟩ := hu.exists_finiteMeasure_poissonKernel_eq hpos
  let G : ℂ → ℂ := fun w => ∫ ξ : Circle, herglotzRieszKernel 0 w ξ ∂(μ : Measure Circle)
  have hi (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      Integrable (fun ξ : Circle => herglotzRieszKernel 0 w ξ) (μ : Measure Circle) :=
    (continuous_herglotzRieszKernel_circle hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGre (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (G w).re = (f w).re := by
    calc
      (G w).re = ∫ ξ : Circle, (herglotzRieszKernel 0 w ξ).re ∂(μ : Measure Circle) :=
        (Complex.reCLM.integral_comp_comm (hi w hw)).symm
      _ = (f w).re := by
        simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply] using hμ w hw
  have hGanalytic : AnalyticOnNhd ℂ G (ball 0 1) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro w hw
    exact (hasDerivAt_integral_herglotzRieszKernel (μ : Measure Circle) hw).differentiableAt.differentiableWithinAt
  have hzero : ∀ w ∈ ball (0 : ℂ) 1, ((f - G) w).re = 0 := by
    intro w hw
    simp only [Pi.sub_apply, Complex.sub_re, hGre w hw, sub_self]
  obtain ⟨c, hc⟩ := (hf.sub hGanalytic).eq_const_of_re_eq_const hzero isOpen_ball
    ⟨⟨0, by simp⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  have hG0 : G 0 = ((f 0).re : ℂ) := by
    change (∫ ξ : Circle, herglotzRieszKernel 0 0 ξ ∂(μ : Measure Circle)) = _
    have hk (ξ : Circle) : herglotzRieszKernel 0 0 ξ = 1 := by
      simp only [herglotzRieszKernel_def, sub_zero, add_zero, div_self (Circle.coe_ne_zero ξ)]
    simp_rw [hk]
    rw [integral_const, Complex.real_smul, mul_one]
    change ((μ.mass : ℝ) : ℂ) = ((f 0).re : ℂ)
    exact congrArg Complex.ofReal hmass
  have hc0 : c = Complex.I * (f 0).im := by
    have he := hc 0 (by simp)
    change f 0 - G 0 = c at he
    rw [hG0] at he
    rw [← he]
    apply Complex.ext <;> simp
  refine ⟨μ, hmass, ?_⟩
  intro w hw
  have he := hc w hw
  change f w - G w = c at he
  rw [hc0] at he
  change f w = Complex.I * (f 0).im + G w
  linear_combination he

end Complex

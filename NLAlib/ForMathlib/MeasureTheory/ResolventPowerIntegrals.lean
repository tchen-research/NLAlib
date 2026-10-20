import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import NLAlib.ForMathlib.Analysis.Normed.Algebra.ResolventDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual Bochner means of self-adjoint resolvent powers

Every power of a measurable self-adjoint random element has an integrable
nonreal resolvent under a finite measure. The exact power derivative passes
through the actual Bochner integral by a uniform reciprocal-height bound.
The zeroth power, trivial algebra and zero measure are included.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
variable {Ω A : Type*} [MeasurableSpace Ω] [CStarAlgebra A]
  {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem cstar_norm_pow_le (a : A) (n : ℕ) : ‖a^n‖≤‖a‖^n := by
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let := h
    simpa only [Subsingleton.elim (a^n) 0,norm_zero] using pow_nonneg (norm_nonneg a) n
  | inr h =>
    let := h
    exact norm_pow_le a n

namespace selfAdjoint

/-- The genuine nonreal resolvent is continuous on the self-adjoint subtype. -/
theorem continuous_resolvent {z : ℂ} (hz : z.im≠0) :
    Continuous (fun a : selfAdjoint A => resolvent (a : A) z) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hu := a.property.isUnit_algebraMap_sub_of_im_ne_zero hz
  have hi : ContinuousAt Ring.inverse (algebraMap ℂ A z-(a : A)) := by
    simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  change ContinuousAt (fun b : selfAdjoint A => Ring.inverse (algebraMap ℂ A z-(b : A))) a
  exact hi.comp (f := fun b : selfAdjoint A => algebraMap ℂ A z-(b : A))
    ((continuous_const.sub continuous_subtype_val).continuousAt :
    ContinuousAt (fun b : selfAdjoint A => algebraMap ℂ A z-(b : A)) a)

end selfAdjoint

namespace MeasureTheory

/-- Every actual self-adjoint resolvent power is Bochner integrable at nonreal height. -/
theorem integrable_resolvent_selfAdjoint_pow
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    {z : ℂ} (hz : z.im≠0) (n : ℕ) :
    Integrable (fun ω => resolvent (X ω : A) z^n) μ := by
  apply Integrable.of_bound (((selfAdjoint.continuous_resolvent hz).pow n).comp_aestronglyMeasurable hX)
    (|z.im|⁻¹^n)
  exact Filter.Eventually.of_forall fun ω =>
    (cstar_norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _)
      ((X ω).property.norm_resolvent_le hz) n)

/-- Differentiating the actual Bochner mean of a self-adjoint resolvent power
gives the negative exponent times the mean of its next power. -/
theorem hasDerivAt_integral_resolvent_selfAdjoint_pow
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    {z : ℂ} (hz : z.im≠0) (n : ℕ) :
    HasDerivAt (fun w : ℂ => ∫ ω, resolvent (X ω : A) w^n ∂μ)
      (-(n : ℂ)•∫ ω, resolvent (X ω : A) z^(n+1) ∂μ) z := by
  let r : ℝ := |z.im|/2
  have hr : 0<r := by dsimp [r]; exact half_pos (abs_pos.mpr hz)
  have hheight {w : ℂ} (hw : w∈Metric.ball z r) : r≤|w.im| := by
    have hd : ‖w-z‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w-z)
    have ha := abs_abs_sub_abs_le_abs_sub w.im z.im
    rw [Complex.sub_im] at hi
    have hlow := (le_abs_self (|w.im|-|z.im|)).trans ha
    have hrev := (neg_le_abs (|w.im|-|z.im|)).trans ha
    dsimp [r] at *
    linarith
  have hne {w : ℂ} (hw : w∈Metric.ball z r) : w.im≠0 :=
    abs_pos.mp (hr.trans_le (hheight hw))
  have hm : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun ω => resolvent (X ω : A) w^n) μ := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact (((selfAdjoint.continuous_resolvent (hne hw)).pow n).comp_aestronglyMeasurable hX)
  have hdm : AEStronglyMeasurable
      (fun ω => -(n : ℂ)•resolvent (X ω : A) z^(n+1)) μ :=
    (((selfAdjoint.continuous_resolvent hz).pow (n+1)).comp_aestronglyMeasurable hX).const_smul _
  have hb : ∀ᵐ ω ∂μ, ∀ w∈Metric.ball z r,
      ‖-(n : ℂ)•resolvent (X ω : A) w^(n+1)‖≤(n : ℝ)*(r⁻¹)^(n+1) := by
    apply Filter.Eventually.of_forall
    intro ω w hw
    rw [norm_smul,norm_neg,Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply (cstar_norm_pow_le _ _).trans
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact ((X ω).property.norm_resolvent_le (hne hw)).trans
      (inv_anti₀ hr (hheight hw))
  have hd : ∀ᵐ ω ∂μ, ∀ w∈Metric.ball z r,
      HasDerivAt (fun v : ℂ => resolvent (X ω : A) v^n)
        (-(n : ℂ)•resolvent (X ω : A) w^(n+1)) w := by
    apply Filter.Eventually.of_forall
    intro ω w hw
    exact spectrum.hasDerivAt_resolvent_pow (X ω : A)
      ((X ω).property.isUnit_algebraMap_sub_of_im_ne_zero (hne hw)) n
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hr) hm (integrable_resolvent_selfAdjoint_pow X hX hz n)
    hdm hb (integrable_const _) hd
  simpa only [integral_smul] using hh.2

end MeasureTheory

import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Logarithmic potentials below a compact support

The logarithmic potential is the actual integral of the real logarithm.
Compact support and separation from the evaluation point provide all the
integrability and differentiation hypotheses. These are scalar prerequisites
for the block-Wishart log-potential formula; they do not assert its global
variational principle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- The real logarithmic potential of a measure. The real logarithm already
uses absolute values, so this is also the integral of `log |x-u|`. As usual
the Bochner integral is total; integrability is supplied by theorems below. -/
def logarithmicPotential (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x, Real.log (x - u) ∂μ

/-- A finite measure with compact support has an integrable logarithmic
kernel at every point strictly below every support point. -/
theorem integrable_log_sub_of_lt_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) {u : ℝ} (hu : ∀ x ∈ μ.support, u < x) :
    Integrable (fun x => Real.log (x - u)) μ := by
  have hc : ContinuousOn (fun x => Real.log (x - u)) μ.support := by
    apply (continuous_id.sub continuous_const).continuousOn.log
    intro x hx
    exact (sub_pos.mpr (hu x hx)).ne'
  have hi := hc.integrableOn_compact (μ := μ) hμ
  have hre : μ.restrict μ.support = μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  rwa [IntegrableOn, hre] at hi

/-- A finite measure with compact support has an integrable real Stieltjes
kernel at every point strictly below every support point. -/
theorem integrable_inv_sub_of_lt_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) {u : ℝ} (hu : ∀ x ∈ μ.support, u < x) :
    Integrable (fun x => (x - u)⁻¹) μ := by
  have hc : ContinuousOn (fun x => (x - u)⁻¹) μ.support := by
    apply (continuous_id.sub continuous_const).continuousOn.inv₀
    intro x hx
    exact (sub_pos.mpr (hu x hx)).ne'
  have hi := hc.integrableOn_compact (μ := μ) hμ
  have hre : μ.restrict μ.support = μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  rwa [IntegrableOn, hre] at hi

/-- Below a compact support, the derivative of the actual logarithmic
potential is minus the actual real Stieltjes transform. No derivative or
integrability of the integral is assumed. This is the differentiation step
in Montanari--Saeed 2026, proof of Theorem 2, equation (45). -/
theorem hasDerivAt_logarithmicPotential_of_lt_support
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {u : ℝ} (hu : ∀ x ∈ μ.support, u < x) :
    HasDerivAt (logarithmicPotential μ) (-(∫ x, (x - u)⁻¹ ∂μ)) u := by
  let F : ℝ → ℝ → ℝ := fun v x => Real.log (x - v)
  let D : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun v x => (-(x-v)⁻¹) • (1 : ℝ →L[ℝ] ℝ)
  let U : Set (ℝ × ℝ) := {p | p.1 < p.2}
  have hU : IsOpen U := isOpen_lt continuous_fst continuous_snd
  have hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) U := by
    apply (continuous_snd.sub continuous_fst).continuousOn.log
    intro p hp
    exact (sub_pos.mpr hp).ne'
  have hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) U := by
    have hi : ContinuousOn (fun p : ℝ × ℝ => (p.2-p.1)⁻¹) U :=
      (continuous_snd.sub continuous_fst).continuousOn.inv₀
        (fun p hp => (sub_pos.mpr hp).ne')
    exact hi.neg.smul continuousOn_const
  have hd (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (fun v => F v p.2) (D p.1 p.2) p.1 := by
    have hh := ((hasDerivAt_const p.1 p.2).sub (hasDerivAt_id p.1)).log
      (sub_pos.mpr hp).ne'
    convert! hh.hasFDerivAt using 1
    ext
    simp [D, div_eq_mul_inv, mul_comm]
  have h := NLAlib.hasFDerivAt_integral_of_compact_support μ hμ F D U hU hF hD hd u hu
  have hDi : Integrable (D u) μ := by
    have hc : ContinuousOn (D u) μ.support :=
      hD.comp (continuous_const.prodMk continuous_id).continuousOn hu
    have hi := hc.integrableOn_compact (μ := μ) hμ
    have hre : μ.restrict μ.support = μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
    rwa [IntegrableOn, hre] at hi
  have hh := h.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hDi] at hh
  convert! hh using 1
  simp [D, integral_neg]

private theorem continuousAt_integral_log_one_add_mul_zero
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support) :
    ContinuousAt (fun v : ℝ => ∫ x, Real.log (1 + v * x) ∂μ) 0 := by
  let F : ℝ → ℝ → ℝ := fun v x => Real.log (1 + v * x)
  let D : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun v x => (x / (1 + v * x)) • (1 : ℝ →L[ℝ] ℝ)
  let U : Set (ℝ × ℝ) := {p | 1 + p.1 * p.2 ≠ 0}
  have harg : Continuous (fun p : ℝ × ℝ => 1 + p.1 * p.2) := by fun_prop
  have hU : IsOpen U := isOpen_ne_fun harg continuous_const
  have hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) U :=
    harg.continuousOn.log (fun _ hp => hp)
  have hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) U :=
    (continuous_snd.continuousOn.div harg.continuousOn (fun _ hp => hp)).smul
      continuousOn_const
  have hd (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (fun v => F v p.2) (D p.1 p.2) p.1 := by
    have hh := (((hasDerivAt_id p.1).mul_const p.2).const_add 1).log hp
    convert! hh.hasFDerivAt using 1
    ext
    simp [D, div_eq_mul_inv, mul_comm]
  have h := NLAlib.hasFDerivAt_integral_of_compact_support μ hμ F D U hU hF hD hd 0
    (fun _ _ => by simp [U])
  exact h.continuousAt

/-- The logarithmic potential of an actual compactly supported probability
measure has its exact normalization at negative infinity. No moment,
integrability, or asymptotic normalization hypothesis is supplied. -/
theorem tendsto_logarithmicPotential_sub_log_neg_atBot
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    Tendsto (fun u => logarithmicPotential μ u - Real.log (-u)) atBot (𝓝 0) := by
  have hcont := continuousAt_integral_log_one_add_mul_zero μ hμ
  have ht : Tendsto (fun u : ℝ => ∫ x, Real.log (1 + (-u)⁻¹ * x) ∂μ)
      atBot (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, zero_mul, add_zero, Real.log_one, integral_zero] using
      hcont.tendsto.comp (tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop)
  obtain ⟨R,hR⟩ := hμ.bddAbove_image continuous_norm.continuousOn
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (min (-R) (-1))] with u hu
  have huR : u < -R := lt_of_lt_of_le hu (min_le_left _ _)
  have hu0 : u < 0 := by
    have hu1 := lt_of_lt_of_le hu (min_le_right (-R) (-1))
    linarith
  have hsupport : ∀ x ∈ μ.support, u < x := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hR ⟨x,hx,rfl⟩
    have hxlo := neg_abs_le x
    rw [Real.norm_eq_abs] at hxR
    linarith
  have hi := integrable_log_sub_of_lt_support μ hμ hsupport
  have he : logarithmicPotential μ u - Real.log (-u) =
      ∫ x, Real.log (x-u) - Real.log (-u) ∂μ := by
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [logarithmicPotential]
  rw [he]
  apply integral_congr_ae
  filter_upwards [μ.support_mem_ae] with x hx
  have harg : 1 + (-u)⁻¹ * x = (x-u)/(-u) := by
    field_simp [hu0.ne]
    ring
  rw [harg, Real.log_div (sub_pos.mpr (hsupport x hx)).ne' (neg_pos.mpr hu0).ne']

/-- On an interval below a compact support, the actual Stieltjes derivative
and the normalization at negative infinity uniquely determine the actual
logarithmic potential. This is the derivative-and-constant argument needed
in the proof of the block-Wishart variational potential identity. -/
theorem eqOn_logarithmicPotential_of_hasDerivAt_of_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (a : ℝ) (ha : ∀ x ∈ μ.support, a ≤ x) (F : ℝ → ℝ)
    (hF : ∀ u < a, HasDerivAt F (-(∫ x, (x-u)⁻¹ ∂μ)) u)
    (hF_infty : Tendsto (fun u => F u - Real.log (-u)) atBot (𝓝 0)) :
    EqOn F (logarithmicPotential μ) (Iio a) := by
  have hL (u : ℝ) (hu : u < a) :=
    hasDerivAt_logarithmicPotential_of_lt_support μ hμ
      (fun x hx => lt_of_lt_of_le hu (ha x hx))
  have hD (u : ℝ) (hu : u < a) :
      HasDerivAt (fun v => F v - logarithmicPotential μ v) 0 u := by
    convert! (hF u hu).sub (hL u hu) using 1
    simp
  obtain ⟨c,hc⟩ := isOpen_Iio.exists_is_const_of_deriv_eq_zero
    (convex_Iio a).isPreconnected
    (fun u hu => (hD u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hD u hu).deriv)
  have ht₀ : Tendsto (fun u => F u - logarithmicPotential μ u) atBot (𝓝 0) := by
    convert hF_infty.sub (tendsto_logarithmicPotential_sub_log_neg_atBot μ hμ) using 1
    · funext u
      ring
    · simp
  have htc : Tendsto (fun u => F u - logarithmicPotential μ u) atBot (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot a] with u hu
    exact (hc u hu).symm
  have hc₀ : c = 0 := tendsto_nhds_unique htc ht₀
  intro u hu
  have hh := hc u hu
  rw [hc₀] at hh
  exact sub_eq_zero.mp hh

end MeasureTheory

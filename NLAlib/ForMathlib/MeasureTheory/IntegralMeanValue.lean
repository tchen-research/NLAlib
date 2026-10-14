import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic

/-! # A weighted integral mean-value theorem without measurable choice

Pointwise intermediate values in one connected real image combine into a single
intermediate value for the integral. The pointwise witnesses need not be measurable.
This is the scalar integral step in derivative remainders for positive quadrature.
-/

open MeasureTheory Set

namespace MeasureTheory

/-- If a measurable integrable quantity is pointwise a value of a continuous function
on a nonempty connected set times a nonnegative integrable weight, its integral is one
such value times the integral of the weight. No measurable selection of the pointwise
intermediate arguments is required, and a zero total weight is included.
Source: integral mean-value argument in operator derivations, (AQ5)–(AQ6). -/
theorem exists_integral_eq_mul_integral_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F W : Ω → ℝ}
    (hF : Integrable F μ) (hW : Integrable W μ) (hWnonneg : ∀ᵐ x ∂μ, 0 ≤ W x)
    {s : Set ℝ} (hs : s.Nonempty) (hsc : IsPreconnected s) {D : ℝ → ℝ}
    (hD : ContinuousOn D s)
    (hpoint : ∀ᵐ x ∂μ, ∃ ξ ∈ s, F x = D ξ * W x) :
    ∃ ξ ∈ s, (∫ x, F x ∂μ) = D ξ * ∫ x, W x ∂μ := by
  by_cases hzero : (∫ x, W x ∂μ) = 0
  · have hWzero := (integral_eq_zero_iff_of_nonneg_ae hWnonneg hW).mp hzero
    have hFzero : F =ᵐ[μ] 0 := by
      filter_upwards [hWzero, hpoint] with x hx hp
      obtain ⟨ξ, _, heq⟩ := hp
      simpa [hx] using heq
    obtain ⟨ξ, hξ⟩ := hs
    exact ⟨ξ, hξ, by simp [integral_congr_ae hFzero, hzero]⟩
  let d := (∫ x, F x ∂μ) / ∫ x, W x ∂μ
  have hbudget : (∫ x, F x ∂μ) = ∫ x, d * W x ∂μ := by
    rw [integral_const_mul]
    dsimp [d]
    field_simp
  by_contra hnone
  have hne : ∀ ξ ∈ s, D ξ ≠ d := by
    intro ξ hξ heq
    apply hnone
    refine ⟨ξ, hξ, ?_⟩
    rw [heq]
    dsimp [d]
    field_simp
  rcases hsc.mapsTo_Ioi_or_Iio hD hne with hgt | hlt
  · have hle : (fun x => d * W x) ≤ᵐ[μ] F := by
      filter_upwards [hWnonneg, hpoint] with x hx hp
      obtain ⟨ξ, hξ, heq⟩ := hp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (hgt hξ).le hx
    have heq := (integral_eq_iff_of_ae_le (hW.const_mul d) hF hle).mp hbudget.symm
    have hWzero : W =ᵐ[μ] 0 := by
      filter_upwards [hWnonneg, hpoint, heq] with x hx hp heqx
      obtain ⟨ξ, hξ, hFx⟩ := hp
      have hmul : (D ξ - d) * W x = 0 := by change d * W x = F x at heqx; nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left (sub_pos.mpr (hgt hξ)).ne'
    exact hzero (by simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hWzero)
  · have hle : F ≤ᵐ[μ] (fun x => d * W x) := by
      filter_upwards [hWnonneg, hpoint] with x hx hp
      obtain ⟨ξ, hξ, heq⟩ := hp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (hlt hξ).le hx
    have heq := (integral_eq_iff_of_ae_le hF (hW.const_mul d) hle).mp hbudget
    have hWzero : W =ᵐ[μ] 0 := by
      filter_upwards [hWnonneg, hpoint, heq] with x hx hp heqx
      obtain ⟨ξ, hξ, hFx⟩ := hp
      have hmul : (d - D ξ) * W x = 0 := by change F x = d * W x at heqx; nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left (sub_pos.mpr (hlt hξ)).ne'
    exact hzero (by simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hWzero)

/-- The weighted integral mean-value theorem also permits a nonpositive weight, by
negating the integrand and weight together. This gives the right-Radau and Lobatto
derivative remainders with their original negative nodal factors. -/
theorem exists_integral_eq_mul_integral_of_pointwise_of_weight_constant_sign
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F W : Ω → ℝ}
    (hF : Integrable F μ) (hW : Integrable W μ)
    (hWsign : (∀ᵐ x ∂μ, 0 ≤ W x) ∨ (∀ᵐ x ∂μ, W x ≤ 0))
    {s : Set ℝ} (hs : s.Nonempty) (hsc : IsPreconnected s) {D : ℝ → ℝ}
    (hD : ContinuousOn D s) (hpoint : ∀ᵐ x ∂μ, ∃ ξ ∈ s, F x = D ξ * W x) :
    ∃ ξ ∈ s, (∫ x, F x ∂μ) = D ξ * ∫ x, W x ∂μ := by
  rcases hWsign with hpos | hneg
  · exact exists_integral_eq_mul_integral_of_pointwise hF hW hpos hs hsc hD hpoint
  · obtain ⟨ξ, hξ, he⟩ := exists_integral_eq_mul_integral_of_pointwise hF.neg hW.neg
      (hneg.mono fun x hx => neg_nonneg.mpr hx) hs hsc hD
      (hpoint.mono fun x hx => by
        obtain ⟨ξ, hξ, he⟩ := hx
        exact ⟨ξ, hξ, by simpa only [Pi.neg_apply, mul_neg] using congrArg Neg.neg he⟩)
    exact ⟨ξ, hξ, by simpa only [integral_neg, Pi.neg_apply, mul_neg, neg_inj] using he⟩

end MeasureTheory

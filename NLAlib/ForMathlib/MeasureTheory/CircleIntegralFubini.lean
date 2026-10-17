import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Finite-interval and circle integration interchange

A jointly continuous kernel on the product of a compact real interval and a
circle satisfies Fubini's theorem for its real interval and complex contour
integrals. Joint integrability is proved from compactness. This supplies the
interchange step toward atlas item `trace-exponential-stahl` (Stahl 2013, Theorem 2).
-/

noncomputable section

open Set MeasureTheory Complex

namespace NLAlib

/-- A jointly continuous kernel has an integrable circle integral as a function
of the real parameter, and the two integrations commute. This supplies both
integrability and Fubini for the density in `trace-exponential-stahl`. -/
theorem intervalIntegrable_circleIntegral_and_integral_circleIntegral_eq
    {F : ℝ → ℂ → ℂ} {a b r : ℝ} {c : ℂ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Metric.sphere c r)) :
    IntervalIntegrable (fun x => ∮ z in C(c, r), F x z) volume a b ∧
    (∫ x in a..b, ∮ z in C(c, r), F x z) =
      ∮ z in C(c, r), ∫ x in a..b, F x z := by
  let H : ℝ × ℝ → ℂ := fun p => deriv (circleMap c r) p.2 * F p.1 (circleMap c r p.2)
  have hc : ContinuousOn H (Icc a b ×ˢ Icc 0 (2 * Real.pi)) := by
    have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, circleMap c r p.2))
        (Icc a b ×ˢ Icc 0 (2 * Real.pi)) (Icc a b ×ˢ Metric.sphere c r) := by
      intro p hp
      exact ⟨hp.1, circleMap_mem_sphere c hr p.2⟩
    have hcomp : ContinuousOn (fun p : ℝ × ℝ => F p.1 (circleMap c r p.2))
        (Icc a b ×ˢ Icc 0 (2 * Real.pi)) :=
      hF.comp (by fun_prop) hmap
    have hd : Continuous (fun p : ℝ × ℝ => deriv (circleMap c r) p.2) := by
      simp only [deriv_circleMap]
      fun_prop
    exact hd.continuousOn.mul hcomp
  have hi : Integrable H
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have heq : (fun x => ∮ z in C(c, r), F x z) =
        fun x => ∫ y in Icc 0 (2 * Real.pi), H (x, y) := by
      funext x
      simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        ← integral_Icc_eq_integral_Ioc, H, smul_eq_mul]
    rw [heq]
    exact hi.integral_prod_left
  have hswap := integral_integral_swap (f := fun x θ => H (x, θ)) hi
  simp_rw [circleIntegral, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  trans ∫ θ in Icc 0 (2 * Real.pi), ∫ x in Icc a b,
    deriv (circleMap c r) θ * F x (circleMap c r θ)
  · simpa only [H, smul_eq_mul] using hswap
  · apply integral_congr_ae
    filter_upwards with θ
    simp only [smul_eq_mul, integral_const_mul]

/-- Integrating a jointly continuous kernel over a finite real interval commutes
with its complex circle integral. The radius is nonnegative and either endpoint
interval may be degenerate.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem integral_circleIntegral_eq_circleIntegral_integral
    {F : ℝ → ℂ → ℂ} {a b r : ℝ} {c : ℂ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Metric.sphere c r)) :
    (∫ x in a..b, ∮ z in C(c, r), F x z) =
      ∮ z in C(c, r), ∫ x in a..b, F x z :=
  (intervalIntegrable_circleIntegral_and_integral_circleIntegral_eq hab hr hF).2

end NLAlib

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import NLAlib.ForMathlib.MeasureTheory.CompactExponential

/-!
# Positive measures from integrable densities on an interval

An integrable real density on a compact interval gives a finite positive
measure by applying `ENNReal.ofReal` and restricting Lebesgue measure. For an
almost everywhere nonnegative density, integration gives precisely its weighted
interval integral. This supplies the measure-construction step after positivity
in the contour approach to atlas `trace-exponential-stahl`.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace NLAlib

/-- The finite positive measure with density `max ρ 0` on `[a,b]` and zero
outside. Almost everywhere nonnegative densities retain their original values.
The integrability argument is used only to certify finite mass. -/
def intervalDensityMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (ρ x)),
    isFiniteMeasure_withDensity_ofReal hρ.2⟩

/-- The underlying measure is restricted Lebesgue measure weighted by the
nonnegative part of the density. -/
theorem intervalDensityMeasure_toMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) :
    (intervalDensityMeasure ρ a b hρ : Measure ℝ) =
      (volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (ρ x)) := rfl

/-- A measure constructed from an interval density is concentrated on that
interval, including a degenerate or empty interval. -/
theorem ae_mem_Icc_intervalDensityMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) :
    ∀ᵐ x ∂(intervalDensityMeasure ρ a b hρ : Measure ℝ), x ∈ Icc a b := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- Integrating against an almost everywhere nonnegative interval density is
its ordinary weighted integral. The test function is arbitrary, with Bochner
integrals interpreted using Mathlib's total integral convention. -/
theorem integral_intervalDensityMeasure {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IntegrableOn ρ (Icc a b))
    (hpos : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ ρ x) (f : ℝ → ℝ) :
    (∫ x, f x ∂(intervalDensityMeasure ρ a b hρ : Measure ℝ)) =
      ∫ x in Icc a b, ρ x * f x := by
  rw [intervalDensityMeasure_toMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- An almost everywhere nonnegative integrable interval density gives a
compact positive exponential representation of its weighted interval integrals. -/
theorem isCompactExpRepresentation_intervalDensityMeasure
    {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : IntegrableOn ρ (Icc a b))
    (hpos : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ ρ x) :
    IsCompactExpRepresentation (intervalDensityMeasure ρ a b hρ)
      (fun t => ∫ x in a..b, Real.exp (t * x) * ρ x) a b := by
  constructor
  · exact ae_mem_Icc_intervalDensityMeasure ρ a b hρ
  · intro t
    rw [integral_intervalDensityMeasure hρ hpos,
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    congr 1
    funext x
    exact mul_comm _ _

namespace IsCompactExpRepresentation

/-- Adding two compactly supported positive exponential measures adds their
represented functions while preserving the common support interval. -/
theorem add {ν₁ ν₂ : FiniteMeasure ℝ} {F₁ F₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : IsCompactExpRepresentation ν₁ F₁ a b)
    (h₂ : IsCompactExpRepresentation ν₂ F₂ a b) :
    IsCompactExpRepresentation (ν₁ + ν₂) (fun t => F₁ t + F₂ t) a b := by
  constructor
  · exact ae_add_measure_iff.mpr ⟨h₁.ae_mem_Icc, h₂.ae_mem_Icc⟩
  · intro t
    rw [FiniteMeasure.toMeasure_add, integral_add_measure (h₁.integrable_exp t)
      (h₂.integrable_exp t), h₁.integral_exp t, h₂.integral_exp t]

end IsCompactExpRepresentation

end NLAlib

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Probability measure on the unit circle

Transport normalized Haar measure from the additive angle circle to the
complex unit circle. Its integrals are exactly the native circle averages.
This supplies the radial positive measures in the Herglotz representation
used by Ajanki--Erdos--Kruger (2019), Proposition 2.1.
-/

noncomputable section

open MeasureTheory Real Complex

namespace Circle

/-- The unit circle carries its Borel measurable space. -/
instance instMeasurableSpace : MeasurableSpace Circle := borel Circle

/-- The canonical measurable space of the unit circle is its Borel space. -/
instance instBorelSpace : BorelSpace Circle := ⟨rfl⟩

private local instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Normalized angle measure on the complex unit circle. -/
def probabilityMeasure : Measure Circle :=
  AddCircle.haarAddCircle.map AddCircle.homeomorphCircle'

/-- Normalized angle measure has total mass one. -/
instance isProbabilityMeasure_probabilityMeasure : IsProbabilityMeasure probabilityMeasure :=
  (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))).isProbabilityMeasure_map
    AddCircle.homeomorphCircle'.continuous.measurable.aemeasurable

/-- Integrating over the complex unit circle is ordinary normalized angle
integration, including for total Bochner integrals. -/
theorem integral_probabilityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Circle → E) :
    (∫ z, f z ∂probabilityMeasure) =
      (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (Circle.exp θ) := by
  change (∫ z, f z ∂(AddCircle.haarAddCircle.map
    AddCircle.homeomorphCircle'.toMeasurableEquiv)) = _
  rw [integral_map_equiv AddCircle.homeomorphCircle'.toMeasurableEquiv]
  rw [AddCircle.integral_haarAddCircle]
  change (2 * π)⁻¹ • (∫ t : AddCircle (2 * π), (f ∘ AddCircle.homeomorphCircle') t) = _
  rw [← AddCircle.intervalIntegral_preimage (2 * π) 0 (f ∘ AddCircle.homeomorphCircle')]
  simp only [zero_add, Function.comp_apply, AddCircle.homeomorphCircle'_apply_mk]

/-- A continuous complex-plane test has the same integral under normalized
unit-circle measure and under the native unit circle average. -/
theorem integral_probabilityMeasure_eq_circleAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ z : Circle, f z ∂probabilityMeasure) = Real.circleAverage f 0 1 := by
  rw [integral_probabilityMeasure, Real.circleAverage_def]
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add, Circle.coe_exp]

end Circle

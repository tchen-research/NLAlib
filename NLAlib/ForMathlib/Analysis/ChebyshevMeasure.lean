import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Chebyshev measure as a cosine pushforward

The unnormalized arcsine measure has mass `π`. Cosine pushes Lebesgue measure
on `(0, π]` to this measure, so finite products admit the same change of variables.
-/

noncomputable section

open MeasureTheory Set Real

namespace Polynomial.Chebyshev

/-- The unnormalized Chebyshev measure is finite, including its integrable
endpoint singularities. -/
instance isFiniteMeasure_measureT : IsFiniteMeasure measureT :=
  (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (integrable_measureT continuousOn_const)

/-- Cosine transports ordinary Lebesgue measure on `(0, π]` to the
unnormalized Chebyshev measure on `(-1,1]`. -/
theorem measurePreserving_cos_chebyshev :
    MeasurePreserving cos (volume.restrict (Ioc (0 : ℝ) π)) measureT := by
  refine ⟨continuous_cos.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map continuous_cos.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_measureT_eq_integral_cos, intervalIntegral.integral_of_le pi_pos.le]

/-- Coordinatewise cosine transports every finite product of angle measures
to the corresponding product of Chebyshev measures. -/
theorem measurePreserving_pi_cos_chebyshev {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun θ : ι → ℝ => fun i => cos (θ i))
      (Measure.pi (fun _ => volume.restrict (Ioc (0 : ℝ) π)))
      (Measure.pi (fun _ => measureT)) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_cos_chebyshev)

end Polynomial.Chebyshev

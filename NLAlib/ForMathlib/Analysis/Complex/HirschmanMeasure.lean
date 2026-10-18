import NLAlib.ForMathlib.Analysis.Complex.HirschmanKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The explicit Hirschman probability measure

The measure is the Lebesgue measure with the displayed density, not an
unspecified boundary distribution. Its Bochner integrals are exactly the
weighted integrals in Sutter--Berta--Tomamichel, arXiv:1604.03023v3 (30).
-/

noncomputable section
open MeasureTheory Set
namespace Real

/-- The actual probability distribution with the exact interior
Stein--Hirschman density, for parameters strictly between zero and one. -/
def hirschmanMeasure (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (hirschmanDensity r t))

/-- The explicit density defines a probability measure, with its mass
computed by its proved antiderivative.
atlas: multivariate-araki-lieb-thirring (partial) -/
theorem isProbabilityMeasure_hirschmanMeasure {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IsProbabilityMeasure (hirschmanMeasure r) := by
  constructor
  rw [hirschmanMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_hirschmanDensity hr)
      (ae_of_all _ (fun t => (hirschmanDensity_pos hr t).le)), integral_hirschmanDensity hr]
  norm_num

/-- Bochner integration against the actual Hirschman probability measure
is exactly integration against the source's scalar density. No separate
integrability premise is needed for this identity.
atlas: multivariate-araki-lieb-thirring (partial) -/
theorem integral_hirschmanMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (f : ℝ → E) :
    ∫ t, f t ∂hirschmanMeasure r = ∫ t, hirschmanDensity r t • f t := by
  rw [hirschmanMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_hirschmanDensity hr).measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hirschmanDensity_pos hr _).le]

end Real

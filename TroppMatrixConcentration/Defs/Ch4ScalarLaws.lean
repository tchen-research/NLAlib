import TroppMatrixConcentration.Defs.Probability
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

noncomputable section
namespace TroppMatrixConcentration

def standardGaussianLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : Prop :=
  Measure.map g μ = gaussianReal 0 1

def rademacherLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : Ω → ℝ) : Prop :=
  Measure.map r μ = (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)

def gaussianSeriesTail (dimension : ℕ) (v t : ℝ) : ℝ :=
  if v = 0 then (if t = 0 then (dimension : ℝ) else 0)
  else (dimension : ℝ) * Real.exp (-(t ^ 2) / (2 * v))

end TroppMatrixConcentration

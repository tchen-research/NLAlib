import NLAlib.Concentration.Matrix.Defs.Probability
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scalar laws for matrix series

The standard Gaussian and Rademacher laws as predicates, and the Gaussian series tail.

Atlas: `matrix-gaussian-series`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace NLAlib

/-- `g` has the standard Gaussian law under `μ`: `μ.map g = gaussianReal 0 1`. Tropp 2015, §4.1.
atlas: scalar-laws-def -/
def IsStandardGaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : Prop :=
  Measure.map g μ = gaussianReal 0 1

/-- `r` has the Rademacher law under `μ`: `μ.map r = ½ δ₁ + ½ δ₋₁`. Tropp 2015, §4.1.
atlas: rademacher-khintchine, scalar-laws-def -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : Ω → ℝ) : Prop :=
  Measure.map r μ = (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)

/-- The Gaussian-series tail `d · exp (-t²/(2v))`, defined piecewise when `v = 0`. Tropp 2015, Thm
4.1.1. Atlas: `matrix-gaussian-series`.
atlas: matrix-gaussian-series -/
def gaussianSeriesTail (dimension : ℕ) (v t : ℝ) : ℝ :=
  if v = 0 then (if t = 0 then (dimension : ℝ) else 0)
  else (dimension : ℝ) * Real.exp (-(t ^ 2) / (2 * v))

end NLAlib

import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import NLAlib.Probability.Rademacher.Core

/-!
# Scalar laws for matrix series

The Gaussian-series tail. The scalar laws `IsStandardGaussian` and `IsRademacher` live in
`NLAlib.Probability.Gaussian.Basic.StandardGaussian` and `NLAlib.Probability.Rademacher.Core`
(imported here).

Atlas: `matrix-gaussian-series`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace NLAlib

/-- The Gaussian-series tail `d · exp (-t²/(2v))`, defined piecewise when `v = 0`. Tropp 2015, Thm
4.1.1. Atlas: `matrix-gaussian-series`.
atlas: matrix-gaussian-series -/
def gaussianSeriesTail (dimension : ℕ) (v t : ℝ) : ℝ :=
  if v = 0 then (if t = 0 then (dimension : ℝ) else 0)
  else (dimension : ℝ) * Real.exp (-(t ^ 2) / (2 * v))

end NLAlib

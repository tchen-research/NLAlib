import TroppMatrixConcentration.Defs.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace TroppMatrixConcentration

def chernoffCgfCoefficient (L θ : ℝ) : ℝ :=
  if L = 0 then θ else (Real.exp (θ * L) - 1) / L

def chernoffLowerTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε)) (a / L)

def chernoffUpperTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp ε / Real.rpow (1 + ε) (1 + ε)) (a / L)

end TroppMatrixConcentration

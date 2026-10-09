import NLAlib.Concentration.Matrix.Defs.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Matrix Chernoff functions

The cgf coefficient and the lower and upper tails of the matrix Chernoff inequality.

Atlas: `matrix-chernoff`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

noncomputable section
namespace NLAlib

/-- The Chernoff cgf coefficient `(e^{θL} - 1)/L`, equal to `θ` when `L = 0`. Tropp 2015, Lemma 5.4.1.
Atlas: `matrix-chernoff`. -/
def chernoffCgfCoefficient (L θ : ℝ) : ℝ :=
  if L = 0 then θ else (Real.exp (θ * L) - 1) / L

/-- The matrix Chernoff lower tail `d · (e^{-ε}/(1-ε)^{1-ε})^{a/L}`, equal to `d` when `L = 0`. Tropp
2015, eq. (5.1.5). Atlas: `matrix-chernoff`. -/
def chernoffLowerTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε)) (a / L)

/-- The matrix Chernoff upper tail `d · (e^{ε}/(1+ε)^{1+ε})^{a/L}`, equal to `d` when `L = 0`. Tropp
2015, eq. (5.1.6). Atlas: `matrix-chernoff`. -/
def chernoffUpperTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp ε / Real.rpow (1 + ε) (1 + ε)) (a / L)

end NLAlib

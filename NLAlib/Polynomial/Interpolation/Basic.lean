import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-! # Chebyshev grid interpolation vocabulary -/

noncomputable section
open Polynomial Polynomial.Chebyshev Finset
namespace NLAlib

/-- The actual Lagrange interpolant on the canonical Chebyshev extrema grid.
Source: Trefethen, ATAP, Theorems 4.1 and 4.2. -/
def chebyshevInterpolant (f : ℝ → ℝ) (n : ℕ) : ℝ[X] :=
  Lagrange.interpolate (range (n + 1)) (node n) (fun j => f (node n j))

end NLAlib

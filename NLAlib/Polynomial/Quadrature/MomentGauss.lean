import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import Mathlib.LinearAlgebra.Lagrange

/-!
# Gauss data of a finite moment functional

Total nodes and cardinal weights are defined directly from a polynomial
functional. Positive finite Hankel systems give their Gauss interpretation;
representing measures are handled by the measure-facing API.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

/-- Canonical nodes of compressed multiplication for a real moment functional. -/
def momentGaussNodes (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Fin n → ℝ :=
  (isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues

/-- Cardinal weights obtained by evaluating the original moment functional. -/
def momentGaussWeights (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => L (Lagrange.basis univ (momentGaussNodes L n) i)

end NLAlib

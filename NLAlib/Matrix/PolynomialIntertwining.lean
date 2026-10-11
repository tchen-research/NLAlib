import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Polynomial intertwining of rectangular matrices

Polynomial functional calculus preserves an intertwining relation `B * A = A * C`.
This provides the rectangular Gram identity used by polynomial-filter range finding.
-/

noncomputable section

open Polynomial
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Powers preserve rectangular intertwining. Source: the induction in the manuscript
`sa:filter`, used for the polynomial-filter-range-finder target. -/
theorem pow_mul_eq_mul_pow_of_mul_eq {𝕜 : Type*} [Semiring 𝕜]
    {B : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : B * A = A * C) (j : ℕ) : B ^ j * A = A * C ^ j := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ', Matrix.mul_assoc, hj, ← Matrix.mul_assoc, h, Matrix.mul_assoc,
      ← pow_succ']

/-- Polynomial calculus preserves rectangular intertwining. Source: the manuscript
`sa:filter`; standard polynomial functional calculus. -/
theorem aeval_mul_eq_mul_aeval_of_mul_eq {R 𝕜 : Type*}
    [CommSemiring R] [CommSemiring 𝕜] [Algebra R 𝕜]
    {B : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : B * A = A * C) (p : R[X]) :
    aeval B p * A = A * aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial j c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul]
    rw [pow_mul_eq_mul_pow_of_mul_eq h j]

/-- The two rectangular Gram polynomials intertwine through the original matrix.
Source: the manuscript `sa:filter`, its displayed polynomial-intertwining identity. -/
theorem aeval_gram_mul_eq_mul_aeval_gram (A : Matrix m n ℝ) (p : ℝ[X]) :
    aeval (A * Aᵀ) p * A = A * aeval (Aᵀ * A) p :=
  aeval_mul_eq_mul_aeval_of_mul_eq (Matrix.mul_assoc _ _ _) p

/-- Complex rectangular Gram polynomials intertwine through the original matrix.
Source: manuscript `sa:filter`, its complex `A A*`/`A* A` identity. The polynomial
has real coefficients, as in the manuscript. -/
theorem aeval_conjGram_mul_eq_mul_aeval_conjGram (A : Matrix m n ℂ) (p : ℝ[X]) :
    aeval (A * Aᴴ) p * A = A * aeval (Aᴴ * A) p :=
  aeval_mul_eq_mul_aeval_of_mul_eq (Matrix.mul_assoc _ _ _) p

end NLAlib

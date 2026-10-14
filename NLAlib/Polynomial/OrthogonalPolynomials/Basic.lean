import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Orthogonal polynomials of a moment functional

Finite Hankel systems define monic orthogonal polynomials without a global Hilbert-space
instance on polynomials. The functional is bilinear, also over the complex numbers.
Sources: Gautschi (2004), Chapter 1; atlas `formal-orthogonal-polynomials`,
`orthogonal-polynomials-measure-def`, and `hankel-moment-positivity`.
-/

noncomputable section

open Polynomial Finset
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The order-`n` Hankel moment matrix of a scalar polynomial functional.
Source: Gautschi (2004), Chapter 1; the order-zero matrix is empty. -/
def hankelMomentMatrix (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun i j => L (X ^ (i.val + j.val))

/-- The Hankel moment determinant; its order-zero value is one.
Source: Gautschi (2004), Chapter 1. -/
def hankelMomentDet (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜 :=
  (hankelMomentMatrix L n).det

/-- Quasi-definiteness of a polynomial moment functional means all its finite Hankel
systems are nonsingular. This is a bilinear condition, without complex conjugation.
Source: Gautschi (2004), Section 1.3. -/
def QuasiDefinitePolynomialFunctional (L : 𝕜[X] →ₗ[𝕜] 𝕜) : Prop :=
  ∀ n, hankelMomentDet L n ≠ 0

/-- The lower coefficients obtained by solving the monic orthogonality system.
At a singular Hankel matrix this uses Mathlib's total matrix inverse, with no
orthogonality assertion. Source: Gautschi (2004), Chapter 1, moment construction. -/
def orthogonalPolynomialCoefficients (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : Fin n → 𝕜 :=
  (hankelMomentMatrix L n)⁻¹ *ᵥ (fun i => -L (X ^ (n + i.val)))

/-- The lower-degree part of the finite moment-system monic polynomial.
Source: Gautschi (2004), Chapter 1. -/
def orthogonalPolynomialLowerPart (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜[X] :=
  ∑ i : Fin n, monomial i.val (orthogonalPolynomialCoefficients L n i)

/-- The total monic polynomial defined by the finite moment system.
Orthogonality is guaranteed when the order-`n` Hankel determinant is nonzero;
at a singular system only its monic degree normalization is retained.
Source: Gautschi (2004), Chapter 1. -/
def monicOrthogonalPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜[X] :=
  X ^ n + orthogonalPolynomialLowerPart L n

/-- A monic degree-`n` polynomial orthogonal to all lower degrees for the bilinear
moment functional. Source: Gautschi (2004), Chapter 1. -/
structure IsMonicOrthogonalPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (p : 𝕜[X]) : Prop where
  monic : p.Monic
  natDegree_eq : p.natDegree = n
  orthogonal : ∀ q : 𝕜[X], q.degree < n → L (p * q) = 0

/-- The squared bilinear norm of a moment-system monic polynomial.
For a positive real measure this is its squared integral norm; for a complex
functional it is bilinear and need not be real or positive. -/
def orthogonalPolynomialNorm (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜 :=
  L (monicOrthogonalPolynomial L n ^ 2)

/-- The monic recurrence diagonal coefficient, using a total norm quotient.
Its value is zero when the denominator vanishes; recurrence theorems exclude
that case. Source: Gautschi (2004), Theorem 1.27. -/
def orthogonalRecurrenceAlpha (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜 :=
  L (X * monicOrthogonalPolynomial L n ^ 2) / orthogonalPolynomialNorm L n

/-- The monic recurrence subdiagonal coefficient is a ratio of successive squared
norms. Order zero is zero, and division by a zero previous norm is total zero.
This coefficient is the square of a normalized Jacobi off-diagonal coefficient.
Source: Gautschi (2004), Theorem 1.27. -/
def orthogonalRecurrenceBeta (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) : 𝕜 :=
  if n = 0 then 0 else orthogonalPolynomialNorm L n / orthogonalPolynomialNorm L (n - 1)

/-- The lower correction in the finite moment construction has degree strictly less
than its order, including the empty correction at order zero. -/
theorem degree_orthogonalPolynomialLowerPart_lt (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (orthogonalPolynomialLowerPart L n).degree < n := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro i _
  apply mem_degreeLT.mpr
  exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.isLt)

/-- Every moment-system polynomial is monic, even when the system is singular. -/
theorem monic_monicOrthogonalPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (monicOrthogonalPolynomial L n).Monic :=
  monic_X_pow_add (degree_orthogonalPolynomialLowerPart_lt L n)

/-- Every moment-system polynomial has exactly its prescribed degree. -/
@[simp] theorem natDegree_monicOrthogonalPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (monicOrthogonalPolynomial L n).natDegree = n := by
  unfold monicOrthogonalPolynomial
  rw [natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using degree_orthogonalPolynomialLowerPart_lt L n

/-- The order-zero monic moment polynomial is one, including the zero functional. -/
@[simp] theorem monicOrthogonalPolynomial_zero (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    monicOrthogonalPolynomial L 0 = 1 := by
  simp [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart]

/-- The empty Hankel determinant is one, including the zero functional. -/
@[simp] theorem hankelMomentDet_zero (L : 𝕜[X] →ₗ[𝕜] 𝕜) : hankelMomentDet L 0 = 1 := by
  simp [hankelMomentDet]

end NLAlib

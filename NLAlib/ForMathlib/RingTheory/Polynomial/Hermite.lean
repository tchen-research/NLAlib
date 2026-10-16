import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Tactic.Ring

/-! # Differentiation of probabilists' Hermite polynomials

The derivative and three-term recurrence use Mathlib's existing integer
Hermite polynomials. They supply the finite Gaussian polynomial construction.
-/

namespace Polynomial

/-- Differentiating a probabilists' Hermite polynomial lowers its degree. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp [hermite_one, hermite_zero]
  | succ n ih =>
    rw [hermite_succ, derivative_sub, derivative_mul, derivative_X, one_mul,
      ih, derivative_smul]
    calc
      _ = hermite (n + 1) + (n + 1) • (X * hermite n - derivative (hermite n)) := by
        simp only [nsmul_eq_mul]
        ring
      _ = hermite (n + 1) + (n + 1) • hermite (n + 1) := by rw [← hermite_succ]
      _ = _ := by simp only [add_nsmul, one_nsmul]; ac_rfl

/-- Multiplication by the variable is the Hermite raising-plus-lowering
recurrence. This identity is valid over the integer coefficient ring. -/
theorem X_mul_hermite_succ (n : ℕ) :
    X * hermite (n + 1) = hermite (n + 2) + (n + 1) • hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]
  exact (sub_add_cancel _ _).symm

end Polynomial

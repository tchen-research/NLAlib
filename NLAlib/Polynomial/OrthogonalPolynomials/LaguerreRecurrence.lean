import NLAlib.Polynomial.OrthogonalPolynomials.Laguerre

/-!
# The monic classical Laguerre recurrence

The finite Rodrigues operator gives the three-term recurrence for the actual
classical Laguerre polynomials. The order-zero boundary uses the vanishing
coefficient `0^2`, so the same formula applies to every order.
Source: the focused reciprocal exponential reroute, Section 1.
-/

noncomputable section

open Polynomial
open scoped Nat

namespace NLAlib

/-- The classical Laguerre polynomial with leading coefficient one. -/
def monicLaguerrePolynomial (n : ℕ) : ℝ[X] :=
  ((-1 : ℝ)^n * (n ! : ℝ)) • laguerrePolynomial n

private theorem monicLaguerrePolynomial_eq_rodrigues (n : ℕ) :
    monicLaguerrePolynomial n = (-1 : ℝ)^n •
      (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (X ^ n) := by
  rw [monicLaguerrePolynomial, laguerrePolynomial, smul_smul]
  congr 1
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private theorem laguerreRodriguesOperator_X_mul (p : ℝ[X]) :
    laguerreRodriguesOperator (X * p) = X * laguerreRodriguesOperator p + p := by
  simp only [laguerreRodriguesOperator_apply, derivative_mul, derivative_X, one_mul]
  ring

private theorem iterate_laguerreRodriguesOperator_succ_X_mul (n : ℕ) (p : ℝ[X]) :
    (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1] (X * p) =
      X * (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1] p +
        ((n + 1 : ℕ) : ℝ) •
          (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] p := by
  induction n with
  | zero => simpa using laguerreRodriguesOperator_X_mul p
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_smul,
      laguerreRodriguesOperator_X_mul]
    rw [← Function.iterate_succ_apply' (f :=
      (laguerreRodriguesOperator : ℝ[X] → ℝ[X])) n p]
    rw [Function.iterate_succ_apply' (f :=
      (laguerreRodriguesOperator : ℝ[X] → ℝ[X])) (n + 1) p]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      smul_eq_C_mul, map_add, C_1]
    ring

private theorem iterate_laguerreRodriguesOperator_smul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (a • p) =
      a • (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_smul,
      Function.iterate_succ_apply']

private theorem derivative_commute_laguerreRodriguesOperator :
    Function.Commute (derivative : ℝ[X] → ℝ[X]) laguerreRodriguesOperator := by
  intro p
  simp [laguerreRodriguesOperator]

private theorem derivative_iterate_laguerreRodriguesOperator_X_pow_succ (n : ℕ) :
    derivative ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1]
      (X ^ (n + 1))) =
        ((n + 1 : ℕ) : ℝ) •
          (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1] (X ^ n) := by
  rw [(derivative_commute_laguerreRodriguesOperator.iterate_right (n + 1))
    (X ^ (n + 1)), derivative_X_pow_succ, ← smul_eq_C_mul]
  simpa only [Nat.cast_add, Nat.cast_one] using
    iterate_laguerreRodriguesOperator_smul (n + 1) ((n + 1 : ℕ) : ℝ) (X ^ n)

private theorem X_mul_derivative_iterate_laguerreRodriguesOperator_X_pow_succ
    (n : ℕ) :
    X * derivative ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1]
      (X ^ (n + 1))) =
        ((n + 1 : ℕ) : ℝ) •
          (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1] (X ^ (n + 1)) -
        (((n + 1 : ℕ) : ℝ)^2) •
          (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (X ^ n) := by
  have h := iterate_laguerreRodriguesOperator_succ_X_mul n (X ^ n)
  rw [← pow_succ'] at h
  rw [derivative_iterate_laguerreRodriguesOperator_X_pow_succ]
  rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
  rw [h]
  simp only [smul_eq_C_mul, map_pow]
  ring

private theorem iterate_laguerreRodriguesOperator_X_pow_succ (n : ℕ) :
    (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n + 1] (X ^ (n + 1)) =
      (C ((n + 1 : ℕ) : ℝ) - X) *
        (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (X ^ n) +
      X * derivative ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (X ^ n)) := by
  rw [pow_succ', iterate_laguerreRodriguesOperator_succ_X_mul,
    Function.iterate_succ_apply', laguerreRodriguesOperator_apply,
    smul_eq_C_mul]
  ring

/-- The order-zero monic classical Laguerre polynomial is one. -/
@[simp] theorem monicLaguerrePolynomial_zero : monicLaguerrePolynomial 0 = 1 := by
  simp [monicLaguerrePolynomial_eq_rodrigues]

/-- The coefficient of degree `n` in the monic classical Laguerre polynomial is one. -/
@[simp] theorem coeff_monicLaguerrePolynomial_self (n : ℕ) :
    (monicLaguerrePolynomial n).coeff n = 1 := by
  rw [monicLaguerrePolynomial, coeff_smul, coeff_laguerrePolynomial_self,
    smul_eq_mul]
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp
  simpa only [pow_two] using hsign

/-- The degree of the monic classical Laguerre polynomial is its order. -/
@[simp] theorem natDegree_monicLaguerrePolynomial (n : ℕ) :
    (monicLaguerrePolynomial n).natDegree = n := by
  apply le_antisymm
  · exact (natDegree_smul_le _ _).trans (by rw [natDegree_laguerrePolynomial])
  · exact le_natDegree_of_ne_zero (by rw [coeff_monicLaguerrePolynomial_self]; norm_num)

/-- The normalized classical Laguerre polynomial is monic. -/
theorem monic_monicLaguerrePolynomial (n : ℕ) : (monicLaguerrePolynomial n).Monic := by
  apply monic_of_degree_le n
  · exact (degree_smul_le _ _).trans (by rw [degree_laguerrePolynomial])
  · exact coeff_monicLaguerrePolynomial_self n

/-- The full polynomial degree of the monic classical Laguerre polynomial is its order. -/
@[simp] theorem degree_monicLaguerrePolynomial (n : ℕ) :
    (monicLaguerrePolynomial n).degree = n := by
  rw [degree_eq_natDegree (monic_monicLaguerrePolynomial n).ne_zero,
    natDegree_monicLaguerrePolynomial]

/-- The actual monic classical Laguerre polynomials satisfy the recurrence with
diagonal coefficient `2n+1` and lower coefficient `n^2`, including order zero.
Source: the focused reciprocal exponential reroute, Section 1. -/
theorem monicLaguerrePolynomial_succ_eq (n : ℕ) :
    monicLaguerrePolynomial (n + 1) =
      (X - C (2 * (n : ℝ) + 1)) * monicLaguerrePolynomial n -
        C ((n : ℝ)^2) * monicLaguerrePolynomial (n - 1) := by
  cases n with
  | zero =>
    simp [monicLaguerrePolynomial_eq_rodrigues,
      laguerreRodriguesOperator_apply]
  | succ n =>
    rw [monicLaguerrePolynomial_eq_rodrigues,
      monicLaguerrePolynomial_eq_rodrigues,
      monicLaguerrePolynomial_eq_rodrigues,
      Nat.add_one_sub_one, iterate_laguerreRodriguesOperator_X_pow_succ,
      X_mul_derivative_iterate_laguerreRodriguesOperator_X_pow_succ]
    simp only [smul_eq_C_mul, map_add, map_mul, map_pow,
      Nat.cast_add, Nat.cast_one, pow_succ, map_neg, C_1, map_ofNat]
    ring

end NLAlib

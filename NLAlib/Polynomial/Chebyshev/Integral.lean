import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-! # Lebesgue moments of Chebyshev polynomials

Exact moments and integration of finite Chebyshev expansions (ATAP Theorem 19.2).
-/

noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory
namespace NLAlib

private theorem derivative_chebyshev_primitive (k : ℕ) :
    derivative (C (1 / (2 * ((k : ℝ) + 3))) * T ℝ ((k : ℤ) + 3) -
      C (1 / (2 * ((k : ℝ) + 1))) * T ℝ ((k : ℤ) + 1)) = T ℝ ((k : ℤ) + 2) := by
  rw [derivative_sub, derivative_C_mul, derivative_C_mul, T_derivative_eq_U,
    T_derivative_eq_U]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
  rw [show (k : ℤ) + 3 - 1 = k + 2 by omega,
    show (k : ℤ) + 1 - 1 = k by omega]
  have h1 : C (1 / (2 * ((k : ℝ) + 3))) * ((k : ℝ[X]) + 3) = C (1 / 2 : ℝ) := by
    rw [← C_eq_natCast, ← C_ofNat, ← C_add, ← Polynomial.C_mul]
    congr 1
    field_simp
  have h2 : C (1 / (2 * ((k : ℝ) + 1))) * ((k : ℝ[X]) + 1) = C (1 / 2 : ℝ) := by
    rw [← C_eq_natCast, ← C_1, ← C_add, ← Polynomial.C_mul]
    congr 1
    field_simp
  rw [← mul_assoc, h1, ← mul_assoc, h2, ← mul_sub,
    ← two_mul_T_eq_U_sub_U, ← mul_assoc, ← C_ofNat, ← Polynomial.C_mul]
  norm_num

private theorem integral_eval_T_add_two (k : ℕ) :
    (∫ x in (-1 : ℝ)..1, (T ℝ ((k : ℤ) + 2)).eval x) =
      (1 - (-1 : ℝ) ^ (k + 3)) / (2 * ((k : ℝ) + 3)) -
      (1 - (-1 : ℝ) ^ (k + 1)) / (2 * ((k : ℝ) + 1)) := by
  let P := C (1 / (2 * ((k : ℝ) + 3))) * T ℝ ((k : ℤ) + 3) -
      C (1 / (2 * ((k : ℝ) + 1))) * T ℝ ((k : ℤ) + 1)
  have hd : derivative P = T ℝ ((k : ℤ) + 2) := derivative_chebyshev_primitive k
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
    (fun x _ => hd ▸ P.hasDerivAt x) ((T ℝ ((k : ℤ) + 2)).continuous.intervalIntegrable _ _)
  rw [h]
  simp only [P, eval_sub, eval_mul, eval_C, T_eval_one, mul_one, T_eval_neg_one]
  rw [show (k : ℤ) + 3 = ((k + 3 : ℕ) : ℤ) by omega,
    show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
    Int.cast_negOnePow_natCast, Int.cast_negOnePow_natCast]
  ring

/-- The unweighted integral of a first-kind Chebyshev polynomial is `2/(1-k²)`
for even `k`, and zero for odd `k`. Source: Trefethen, ATAP, Theorem 19.2.
The cases `k=0,1` are included without a division by zero in the even branch.
atlas: chebyshev-integral-formula -/
theorem integral_eval_T (k : ℕ) :
    (∫ x in (-1 : ℝ)..1, (T ℝ k).eval x) =
      if Even k then 2 / (1 - (k : ℝ) ^ 2) else 0 := by
  rcases k with _ | _ | k
  · norm_num [T_zero]
  · norm_num [T_one, integral_id]
  · rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by omega, integral_eval_T_add_two]
    by_cases hk : Even (k + 2)
    · have hk1 : Odd (k + 1) := by simpa using (show Even k by simpa [Nat.even_add] using hk).add_one
      have hk3 : Odd (k + 3) := by simpa [Nat.add_assoc] using hk1.add_even (show Even 2 by decide)
      rw [if_pos hk, hk1.neg_one_pow, hk3.neg_one_pow]
      push_cast
      norm_num only [sub_neg_eq_add, one_add_one_eq_two]
      rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
      have h0 : (k : ℝ) + 1 ≠ 0 := by positivity
      have h1 : (k : ℝ) + 3 ≠ 0 := by positivity
      have h2 : 1 - ((k : ℝ) + 2) ^ 2 ≠ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      field_simp [h0, h1, h2]
      ring
    · have hk1 : Even (k + 1) := by simpa [Nat.even_add] using hk
      have hk3 : Even (k + 3) := by simpa [Nat.add_assoc] using hk1.add (show Even 2 by decide)
      rw [if_neg hk, hk1.neg_one_pow, hk3.neg_one_pow]
      simp

/-- Integrating a finite Chebyshev expansion amounts to summing its even moments.
Source: Trefethen, ATAP, Theorem 19.2.
atlas: chebyshev-integral-formula -/
theorem integral_sum_mul_eval_T {ι : Type*} (s : Finset ι) (c : ι → ℝ) (k : ι → ℕ) :
    (∫ x in (-1 : ℝ)..1, ∑ i ∈ s, c i * (T ℝ (k i)).eval x) =
      ∑ i ∈ s, if Even (k i) then 2 * c i / (1 - (k i : ℝ) ^ 2) else 0 := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_eval_T]
    split_ifs <;> ring
  · intro i hi
    exact (continuous_const.mul (T ℝ (k i)).continuous).intervalIntegrable _ _

end NLAlib

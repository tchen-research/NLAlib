import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Positivity of a monic polynomial with degree-dependent signed coefficients

After reversing signs by the coefficient degree, evaluating at a negative
positive magnitude has a fixed nonzero sign. This elementary fact excludes
negative roots in the PSD characteristic-polynomial criterion.
-/

noncomputable section
open Polynomial

namespace NLAlib

private theorem signed_mul_neg_pow {N j : ℕ} (hj : j ≤ N) (c t : ℝ) :
    (-1 : ℝ) ^ N * (c * (-t) ^ j) = ((-1 : ℝ) ^ (N - j) * c) * t ^ j := by
  have hp : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add, show j + j = 2 * j by omega, pow_mul, neg_one_sq, one_pow]
  have hpow : (-1 : ℝ) ^ N = (-1 : ℝ) ^ (N - j) * (-1 : ℝ) ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hnegpow : (-t) ^ j = (-1 : ℝ) ^ j * t ^ j := neg_pow t j
  rw [hpow, hnegpow]
  calc
    _ = (((-1 : ℝ) ^ (N - j) * c) * t ^ j) *
        ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by ring
    _ = _ := by rw [hp, mul_one]

/-- A monic real polynomial whose coefficients have the expected
degree-dependent signs cannot vanish at a negative real argument.
Scalar polynomial positivity; helper for `sylvester-criterion`. -/
theorem mul_eval_neg_pos_of_signed_coeff_nonneg {p : ℝ[X]} {N : ℕ}
    (hdeg : p.natDegree = N) (hp : p.Monic)
    (hcoeff : ∀ j, j ≤ N → 0 ≤ (-1 : ℝ) ^ (N - j) * p.coeff j)
    {t : ℝ} (ht : 0 < t) : 0 < (-1 : ℝ) ^ N * p.eval (-t) := by
  rw [Polynomial.eval_eq_sum_range, hdeg, Finset.mul_sum]
  apply Finset.sum_pos'
  · intro j hj
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [signed_mul_neg_pow hjN]
    exact mul_nonneg (hcoeff j hjN) (pow_nonneg ht.le _)
  · refine ⟨N, Finset.mem_range.mpr (Nat.lt_succ_self N), ?_⟩
    rw [signed_mul_neg_pow le_rfl, Nat.sub_self, pow_zero, one_mul]
    have hN : p.coeff N = 1 := by simpa only [hdeg] using hp.coeff_natDegree
    rw [hN, one_mul]
    exact pow_pos ht N

end NLAlib

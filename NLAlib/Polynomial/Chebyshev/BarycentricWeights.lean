import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Lagrange

/-! # Chebyshev endpoint-grid barycentric weights

The nodal polynomial and the Salzer weights on the `n+1` endpoint grid.
-/
noncomputable section
open Polynomial Polynomial.Chebyshev Finset Real
namespace NLAlib

private theorem eval_U_node_succ_eq_zero {k j : ℕ} (hj0 : 0 < j) (hj : j < k + 1) :
    (U ℝ k).eval (node (k + 1) j) = 0 := by
  have ht0 : 0 < (j : ℝ) * Real.pi / (k + 1) := by positivity
  have ht1 : (j : ℝ) * Real.pi / (k + 1) < Real.pi := by
    have h : (j : ℝ) < k + 1 := by exact_mod_cast hj
    have hn : (0 : ℝ) < k + 1 := by positivity
    apply (div_lt_iff₀ hn).mpr
    nlinarith [Real.pi_pos]
  have h := U_real_cos ((j : ℝ) * Real.pi / (k + 1)) (k : ℤ)
  have ht : ((k : ℤ) + 1 : ℝ) * ((j : ℝ) * Real.pi / (k + 1)) = j * Real.pi := by
    push_cast
    field_simp
  rw [ht, sin_nat_mul_pi, mul_eq_zero] at h
  simpa [node] using h.resolve_right (ne_of_gt (sin_pos_of_pos_of_lt_pi ht0 ht1))

/-- The monic endpoint-grid node polynomial is the scaled `(X²−1)U_{n−1}`.
Source: Trefethen, ATAP, Exercise 4.1; equivalent form of the node-polynomial
identity in `chebyshev-barycentric-weights`.
atlas: chebyshev-barycentric-weights (partial) -/
theorem nodal_node_succ (k : ℕ) :
    Lagrange.nodal (range (k + 2)) (node (k + 1)) =
      C (1 / 2 ^ k : ℝ) * ((X ^ 2 - 1) * U ℝ k) := by
  have hXdeg : ((X : ℝ[X]) ^ 2 - 1).degree = 2 := by
    simpa using degree_X_pow_sub_C (R := ℝ) (n := 2) (by decide) 1
  have hXlead : ((X : ℝ[X]) ^ 2 - 1).leadingCoeff = 1 := by
    simpa only [Polynomial.Monic, C_1] using monic_X_pow_sub_C (R := ℝ) 1 (n := 2) (by decide)
  have hdeg : (C (1 / 2 ^ k : ℝ) * ((X ^ 2 - 1) * U ℝ k)).degree = ((k + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul (by positivity), degree_mul,
      hXdeg,
      degree_U_natCast]
    push_cast
    ring
  have hlead : (C (1 / 2 ^ k : ℝ) * ((X ^ 2 - 1) * U ℝ k)).leadingCoeff = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul,
      hXlead,
      leadingCoeff_U_natCast]
    field_simp
  apply eq_of_degree_le_of_eval_index_eq (range (k + 2)) (strictAntiOn_node (k + 1)).injOn
  · simp
  · simpa using hdeg.symm
  · have hnod : (Lagrange.nodal (range (k + 2)) (node (k + 1))).leadingCoeff = 1 :=
      Lagrange.nodal_monic
    rw [hnod, hlead]
  · intro j hj
    rw [Lagrange.eval_nodal_at_node hj, eval_mul, eval_C, eval_mul, eval_sub, eval_pow,
      eval_X, eval_one]
    by_cases hj0 : j = 0
    · simp [hj0, node_eq_one]
    by_cases hjn : j = k + 1
    · rw [hjn, node_eq_neg_one (n := k + 1) (by omega)]
      norm_num
    rw [eval_U_node_succ_eq_zero (by omega) (by simpa using (show j < k + 1 by
      have h := mem_range.mp hj
      omega)), mul_zero, mul_zero]

private theorem eval_derivative_nodal_node_succ (k j : ℕ) (hj : j ∈ range (k + 2)) :
    (derivative (Lagrange.nodal (range (k + 2)) (node (k + 1)))).eval (node (k + 1) j) =
      (1 / 2 ^ k : ℝ) * (k + 1) * (-1) ^ j * (if j = 0 ∨ j = k + 1 then 2 else 1) := by
  rw [nodal_node_succ, derivative_C_mul, derivative_mul]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero,
    eval_mul, eval_C, eval_add, eval_sub, eval_pow, eval_X, eval_one]
  by_cases hj0 : j = 0
  · subst j
    rw [node_eq_one, U_eval_one]
    simp
    ring
  by_cases hjn : j = k + 1
  · subst j
    rw [node_eq_neg_one (n := k + 1) (by omega), U_eval_neg_one]
    simp only [Int.cast_negOnePow_natCast, Int.cast_natCast]
    simp [pow_succ]
    ring
  rw [if_neg (not_or.mpr ⟨hj0, hjn⟩), mul_one,
    eval_U_node_succ_eq_zero (by omega) (by have h := mem_range.mp hj; omega), mul_zero,
    zero_add]
  have h := congrArg (fun P : ℝ[X] => P.eval (node (k + 1) j))
    (add_one_mul_T_eq_poly_in_U (R := ℝ) k)
  simp only [eval_mul, eval_add, eval_sub, eval_one, eval_X, eval_pow, eval_natCast,
    Int.cast_natCast] at h
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
    eval_T_real_node (by simpa using (show j ≤ k + 1 by
      have h := mem_range.mp hj
      omega)), eval_U_node_succ_eq_zero (by omega)
        (by have h := mem_range.mp hj; omega), mul_zero] at h
  linear_combination -(1 / 2 ^ k : ℝ) * h

/-- The endpoint-grid barycentric weights are `2^(n−1)/n` times alternating signs,
with the first and last weights halved. Source: Trefethen, ATAP, Theorem 5.2
(Salzer's formula). The grid has `n=k+1≥1`, so its denominator is nonzero.
atlas: chebyshev-barycentric-weights -/
theorem nodalWeight_node_succ (k j : ℕ) (hj : j ∈ range (k + 2)) :
    Lagrange.nodalWeight (range (k + 2)) (node (k + 1)) j =
      (2 ^ k / (k + 1) : ℝ) * (-1) ^ j * (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hj, eval_derivative_nodal_node_succ k j hj]
  have hn : (k : ℝ) + 1 ≠ 0 := by positivity
  have hs : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  have hsq : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
  split_ifs <;> field_simp [hn, hs] <;> nlinarith [hsq]

/-- The endpoint-grid nodal polynomial is `2^(-n)(T_{n+1}−T_{n−1})`.
Source: Trefethen, ATAP, Exercise 4.1. The degree-one case is included with `n=k+1`.
atlas: chebyshev-barycentric-weights -/
theorem nodal_node_succ_eq_sub_T (k : ℕ) :
    Lagrange.nodal (range (k + 2)) (node (k + 1)) =
      C (1 / 2 ^ (k + 1) : ℝ) * (T ℝ ((k : ℤ) + 2) - T ℝ k) := by
  have hdiff : T ℝ ((k : ℤ) + 2) - T ℝ k = 2 * ((X ^ 2 - 1) * U ℝ k) := by
    have h1 := T_sub_one ℝ ((k : ℤ) + 1)
    have h2 := T_eq_X_mul_T_sub_pol_U ℝ k
    rw [show (k : ℤ) + 1 - 1 = k by omega,
      show (k : ℤ) + 1 + 1 = k + 2 by omega] at h1
    linear_combination -h1 + 2 * h2
  rw [nodal_node_succ, hdiff, ← C_ofNat]
  rw [← mul_assoc (C (1 / 2 ^ (k + 1) : ℝ)) (C (2 : ℝ)), ← Polynomial.C_mul]
  congr 1
  rw [pow_succ]
  field_simp

/-- The Chebyshev endpoint-grid interpolant has the barycentric formula with
alternating endpoint-halved weights. Source: Trefethen, ATAP, Theorem 5.2.
At grid nodes the interpolant is instead evaluated by its interpolation property.
atlas: chebyshev-barycentric-weights -/
theorem eval_interpolate_node_succ_eq_barycentric (k : ℕ) (f : ℕ → ℝ) {x : ℝ}
    (hx : ∀ j ∈ range (k + 2), x ≠ node (k + 1) j) :
    (Lagrange.interpolate (range (k + 2)) (node (k + 1)) f).eval x =
      (∑ j ∈ range (k + 2), (-1 : ℝ) ^ j * (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) *
        (x - node (k + 1) j)⁻¹ * f j) /
      (∑ j ∈ range (k + 2), (-1 : ℝ) ^ j * (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) *
        (x - node (k + 1) j)⁻¹) := by
  rw [Lagrange.eval_interpolate_not_at_node' f (strictAntiOn_node (k + 1)).injOn
    (by simp) hx]
  have hw (j : ℕ) (hj : j ∈ range (k + 2)) := nodalWeight_node_succ k j hj
  have hnum := Finset.sum_congr rfl (fun j hj => congrArg
    (fun w : ℝ => w * (x - node (k + 1) j)⁻¹ * f j) (hw j hj))
  have hden := Finset.sum_congr rfl (fun j hj => congrArg
    (fun w : ℝ => w * (x - node (k + 1) j)⁻¹) (hw j hj))
  rw [hnum, hden]
  have hN : (∑ j ∈ range (k + 2), (2 ^ k / (k + 1) : ℝ) * (-1) ^ j *
      (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) * (x - node (k + 1) j)⁻¹ * f j) =
      (2 ^ k / (k + 1) : ℝ) * (∑ j ∈ range (k + 2), (-1) ^ j *
      (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) * (x - node (k + 1) j)⁻¹ * f j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hD : (∑ j ∈ range (k + 2), (2 ^ k / (k + 1) : ℝ) * (-1) ^ j *
      (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) * (x - node (k + 1) j)⁻¹) =
      (2 ^ k / (k + 1) : ℝ) * (∑ j ∈ range (k + 2), (-1) ^ j *
      (if j = 0 ∨ j = k + 1 then 1 / 2 else 1) * (x - node (k + 1) j)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hN, hD, mul_div_mul_left]
  positivity

end NLAlib

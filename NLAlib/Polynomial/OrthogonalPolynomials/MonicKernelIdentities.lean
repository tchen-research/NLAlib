import NLAlib.Polynomial.OrthogonalPolynomials.Kernel
import NLAlib.Polynomial.OrthogonalPolynomials.Orthonormal
import Mathlib.Algebra.BigOperators.Intervals

/-! # Weighted monic and strictly positive confluent kernels

The norm ratios telescope over any finite interval of polynomial orders. They
give the product-weighted monic Christoffel–Darboux identity, and positive real
norms identify its diagonal kernel with a strictly positive orthonormal square sum.
The monic confluent identity remains valid at finite-support termination.
-/

noncomputable section
open Polynomial Finset

namespace NLAlib

/-- Monic recurrence norm ratios telescope between any two orders, including
a zero terminal norm. Source: operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem orthogonalPolynomialNorm_mul_prod_beta_eq {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    orthogonalPolynomialNorm L k *
      (∏ i ∈ Ico (k + 1) (n + 1), orthogonalRecurrenceBeta L i) =
        orthogonalPolynomialNorm L n := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst k; simp
    have hkn' : k ≤ n := by omega
    have hH : orthogonalPolynomialNorm L n ≠ 0 :=
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
        (hL n (by omega))).functional_sq_ne_zero (hL (n + 1) le_rfl)
    rw [prod_Ico_succ_top (by omega : k + 1 ≤ n + 1), ← mul_assoc,
      ih (fun j hj => hL j (by omega)) k hkn', orthogonalRecurrenceBeta,
      if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    exact mul_div_cancel₀ _ hH

/-- The monic Christoffel–Darboux identity has the explicit products of monic
recurrence coefficients, and holds also at coinciding arguments without division.
Source: Gautschi (2004), Theorem 1.32; operator derivations (OF10).
atlas: monic-orthogonal-recurrence (partial) -/
theorem sub_mul_sum_prod_beta_mul_eval_monicOrthogonalPolynomial {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ j ≤ n + 1, hankelMomentDet L j ≠ 0)
    (x y : 𝕜) :
    (x - y) * (∑ k ∈ range (n + 1),
      (∏ i ∈ Ico (k + 1) (n + 1), orthogonalRecurrenceBeta L i) *
        (monicOrthogonalPolynomial L k).eval x * (monicOrthogonalPolynomial L k).eval y) =
      (monicOrthogonalPolynomial L (n + 1)).eval x * (monicOrthogonalPolynomial L n).eval y -
        (monicOrthogonalPolynomial L n).eval x * (monicOrthogonalPolynomial L (n + 1)).eval y := by
  have hH (k : ℕ) (hk : k ≤ n) : orthogonalPolynomialNorm L k ≠ 0 :=
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
      (hL k (by omega))).functional_sq_ne_zero (hL (k + 1) (by omega))
  have hs : orthogonalPolynomialNorm L n *
      (monicOrthogonalKernelPolynomial L (n + 1) y).eval x =
      ∑ k ∈ range (n + 1),
        (∏ i ∈ Ico (k + 1) (n + 1), orthogonalRecurrenceBeta L i) *
          (monicOrthogonalPolynomial L k).eval x * (monicOrthogonalPolynomial L k).eval y := by
    simp only [monicOrthogonalKernelPolynomial, eval_finsetSum, eval_mul, eval_C, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hprod := orthogonalPolynomialNorm_mul_prod_beta_eq L n
      (fun j hj => hL j (by omega)) k (by have := mem_range.mp hk; omega)
    rw [← hprod]
    field_simp [hH k (by have := mem_range.mp hk; omega)]
  rw [← hs]
  have h := sub_mul_eval_monicOrthogonalKernelPolynomial n hL x y
  field_simp [hH n le_rfl] at h
  linear_combination h

/-- A normalized moment polynomial's squared value is its monic squared value
divided by the positive monic norm. -/
theorem sq_eval_orthonormalMomentPolynomial {L : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ}
    (hH : 0 < orthogonalPolynomialNorm L n) (x : ℝ) :
    (orthonormalMomentPolynomial L n).eval x ^ 2 =
      (monicOrthogonalPolynomial L n).eval x ^ 2 / orthogonalPolynomialNorm L n := by
  simp only [orthonormalMomentPolynomial, eval_mul, eval_C, mul_pow, inv_pow]
  rw [Real.sq_sqrt hH.le]
  ring

/-- The diagonal monic kernel is exactly the square sum of the normalized
polynomials, and is strictly positive because of the constant term. The top
monic polynomial may be terminal: no normalization at order `n+1` is used.
Source: Gautschi (2004), Corollary to Theorem 1.32; operator derivations (OF11).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem sum_sq_eval_orthonormalMomentPolynomial_eq_confluent_and_pos
    (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) (hL : ∀ j ≤ n + 1, hankelMomentDet L j ≠ 0)
    (hH : ∀ j ≤ n, 0 < orthogonalPolynomialNorm L j) (x : ℝ) :
    (∑ k ∈ range (n + 1), (orthonormalMomentPolynomial L k).eval x ^ 2) =
      ((monicOrthogonalPolynomial L (n + 1)).derivative.eval x *
        (monicOrthogonalPolynomial L n).eval x -
        (monicOrthogonalPolynomial L n).derivative.eval x *
          (monicOrthogonalPolynomial L (n + 1)).eval x) / orthogonalPolynomialNorm L n ∧
      0 < ∑ k ∈ range (n + 1), (orthonormalMomentPolynomial L k).eval x ^ 2 := by
  have he : (∑ k ∈ range (n + 1), (orthonormalMomentPolynomial L k).eval x ^ 2) =
      (monicOrthogonalKernelPolynomial L (n + 1) x).eval x := by
    simp only [monicOrthogonalKernelPolynomial, eval_finsetSum, eval_mul, eval_C]
    apply sum_congr rfl
    intro k hk
    rw [sq_eval_orthonormalMomentPolynomial (hH k (by have := mem_range.mp hk; omega))]
    ring
  refine ⟨he.trans (eval_monicOrthogonalKernelPolynomial_self n hL x), ?_⟩
  apply sum_pos' (fun k _ => sq_nonneg _)
  refine ⟨0, mem_range.mpr (Nat.succ_pos n), ?_⟩
  rw [sq_eval_orthonormalMomentPolynomial (hH 0 (by omega))]
  simp only [monicOrthogonalPolynomial_zero, eval_one, one_pow]
  exact div_pos zero_lt_one (hH 0 (by omega))

/-- When the next norm is positive, the strictly positive confluent kernel has
the fully normalized square-root-beta Wronskian form. At a zero next norm the
preceding monic norm-divided theorem is used instead.
Source: Gautschi (2004), Corollary to Theorem 1.32; operator derivations (OF11).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem sum_sq_eval_orthonormalMomentPolynomial_eq_normalized_confluent_and_pos
    (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) (hL : ∀ j ≤ n + 1, hankelMomentDet L j ≠ 0)
    (hH : ∀ j ≤ n + 1, 0 < orthogonalPolynomialNorm L j) (x : ℝ) :
    (∑ k ∈ range (n + 1), (orthonormalMomentPolynomial L k).eval x ^ 2) =
      Real.sqrt (orthogonalRecurrenceBeta L (n + 1)) *
        ((orthonormalMomentPolynomial L (n + 1)).derivative.eval x *
          (orthonormalMomentPolynomial L n).eval x -
          (orthonormalMomentPolynomial L n).derivative.eval x *
            (orthonormalMomentPolynomial L (n + 1)).eval x) ∧
      0 < ∑ k ∈ range (n + 1), (orthonormalMomentPolynomial L k).eval x ^ 2 := by
  have he := sum_sq_eval_orthonormalMomentPolynomial_eq_confluent_and_pos L n hL
    (fun j hj => hH j (by omega)) x
  have hc : Real.sqrt (orthogonalRecurrenceBeta L (n + 1)) *
      (Real.sqrt (orthogonalPolynomialNorm L (n + 1)))⁻¹ *
        (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ = (orthogonalPolynomialNorm L n)⁻¹ := by
    rw [orthogonalRecurrenceBeta, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel,
      Real.sqrt_div (hH (n + 1) le_rfl).le]
    field_simp [(Real.sqrt_pos.mpr (hH (n + 1) le_rfl)).ne',
      (Real.sqrt_pos.mpr (hH n (by omega))).ne', (hH n (by omega)).ne']
    exact (Real.sq_sqrt (hH n (by omega)).le).symm
  refine ⟨?_, he.2⟩
  rw [he.1]
  simp only [orthonormalMomentPolynomial, derivative_C_mul, eval_mul, eval_C]
  linear_combination
    -((monicOrthogonalPolynomial L (n + 1)).derivative.eval x *
      (monicOrthogonalPolynomial L n).eval x -
      (monicOrthogonalPolynomial L n).derivative.eval x *
        (monicOrthogonalPolynomial L (n + 1)).eval x) * hc

end NLAlib

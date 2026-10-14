import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence

/-! # Monic norms and Christoffel–Darboux kernels

The kernel is defined as a polynomial in its first argument. Its multiplied
Christoffel–Darboux identity has no exceptional diagonal; differentiating it
provides the confluent formula without dividing by a vanishing difference.
Source: Gautschi (2004), Theorems 1.27 and 1.28.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The monic norm equals the mass times the product of positive-order monic
recurrence subdiagonals. Source: Gautschi (2004), Theorem 1.27.
atlas: monic-orthogonal-recurrence (partial) -/
theorem orthogonalPolynomialNorm_eq_prod_beta
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (n : ℕ) (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) :
    orthogonalPolynomialNorm L n = orthogonalPolynomialNorm L 0 *
      ∏ i ∈ range n, orthogonalRecurrenceBeta L (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnorm : orthogonalPolynomialNorm L n ≠ 0 :=
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n (by omega))).functional_sq_ne_zero
        (hL (n + 1) le_rfl)
    rw [prod_range_succ, ← mul_assoc, ← ih (fun k hk => hL k (by omega)), orthogonalRecurrenceBeta,
      if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    exact (mul_div_cancel₀ _ hnorm).symm

/-- The monic reproducing kernel as a polynomial in its first argument; the
sum is empty at order zero. -/
def monicOrthogonalKernelPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (y : 𝕜) : 𝕜[X] :=
  ∑ i ∈ range n, C ((monicOrthogonalPolynomial L i).eval y /
    orthogonalPolynomialNorm L i) * monicOrthogonalPolynomial L i

/-- Multiplying by the argument difference gives the Christoffel–Darboux
identity, with no distinct-argument hypothesis. Source: Gautschi (2004),
Theorem 1.28.
atlas: monic-orthogonal-recurrence (partial) -/
theorem X_sub_C_mul_monicOrthogonalKernelPolynomial
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (n : ℕ) (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) (y : 𝕜) :
    (X - C y) * monicOrthogonalKernelPolynomial L (n + 1) y =
      C ((monicOrthogonalPolynomial L n).eval y / orthogonalPolynomialNorm L n) *
        monicOrthogonalPolynomial L (n + 1) -
      C ((monicOrthogonalPolynomial L (n + 1)).eval y / orthogonalPolynomialNorm L n) *
        monicOrthogonalPolynomial L n := by
  let P := monicOrthogonalPolynomial L
  let H := orthogonalPolynomialNorm L
  induction n with
  | zero =>
    have hr := monicOrthogonalPolynomial_succ_eq L 0 hL
    simp [orthogonalRecurrenceBeta] at hr
    simp only [monicOrthogonalKernelPolynomial, Nat.zero_add, range_one, sum_singleton,
      monicOrthogonalPolynomial_zero, eval_one, mul_one]
    rw [hr]
    simp only [eval_sub, eval_X, eval_C]
    simp only [div_eq_mul_inv, map_mul, map_sub, map_one]
    ring
  | succ n ih =>
    have hH (i : ℕ) (hi : i ≤ n + 1) : H i ≠ 0 :=
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL i (by omega))).functional_sq_ne_zero
        (hL (i + 1) (by omega))
    have hr := monicOrthogonalPolynomial_succ_eq L (n + 1) hL
    have hre := congrArg (eval y) hr
    simp only [eval_sub, eval_mul, eval_X, eval_C, Nat.add_sub_cancel] at hre
    have hb : orthogonalRecurrenceBeta L (n + 1) / H (n + 1) = (H n)⁻¹ := by
      rw [orthogonalRecurrenceBeta, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
      change H (n + 1) / H n / H (n + 1) = _
      field_simp [hH n (by omega), hH (n + 1) le_rfl]
    change (X - C y) * (∑ i ∈ range (n + 1 + 1), C ((P i).eval y / H i) * P i) = _
    rw [sum_range_succ, mul_add]
    change (X - C y) * monicOrthogonalKernelPolynomial L (n + 1) y + _ = _
    rw [ih (fun k hk => hL k (by omega)), hre, hr]
    simp only [P, H, div_eq_mul_inv, map_mul, map_sub, Nat.add_sub_cancel]
    have hbC := congrArg (C : 𝕜 →+* 𝕜[X]) hb
    simp only [H, div_eq_mul_inv, map_mul] at hbC
    linear_combination
      -(C ((monicOrthogonalPolynomial L n).eval y) *
        monicOrthogonalPolynomial L (n + 1) -
        C ((monicOrthogonalPolynomial L (n + 1)).eval y) *
        monicOrthogonalPolynomial L n) * hbC

/-- The scalar multiplied Christoffel–Darboux formula includes coinciding
arguments. Source: Gautschi (2004), Theorem 1.28.
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem sub_mul_eval_monicOrthogonalKernelPolynomial
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (n : ℕ) (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) (x y : 𝕜) :
    (x - y) * (monicOrthogonalKernelPolynomial L (n + 1) y).eval x =
      ((monicOrthogonalPolynomial L (n + 1)).eval x *
        (monicOrthogonalPolynomial L n).eval y -
        (monicOrthogonalPolynomial L n).eval x *
          (monicOrthogonalPolynomial L (n + 1)).eval y) /
        orthogonalPolynomialNorm L n := by
  have h := congrArg (eval x) (X_sub_C_mul_monicOrthogonalKernelPolynomial n hL y)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  rw [h]
  ring

/-- At coinciding arguments the kernel is the derivative Wronskian divided
by the last monic norm. Source: Gautschi (2004), Theorem 1.28.
atlas: monic-orthogonal-recurrence (partial) -/
theorem eval_monicOrthogonalKernelPolynomial_self
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (n : ℕ) (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) (x : 𝕜) :
    (monicOrthogonalKernelPolynomial L (n + 1) x).eval x =
      ((monicOrthogonalPolynomial L (n + 1)).derivative.eval x *
        (monicOrthogonalPolynomial L n).eval x -
        (monicOrthogonalPolynomial L n).derivative.eval x *
          (monicOrthogonalPolynomial L (n + 1)).eval x) /
        orthogonalPolynomialNorm L n := by
  have h := congrArg (fun p : 𝕜[X] => p.derivative.eval x)
    (X_sub_C_mul_monicOrthogonalKernelPolynomial n hL x)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, zero_mul, zero_add, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, sub_self, zero_mul, add_zero] at h
  rw [h]
  ring

end NLAlib

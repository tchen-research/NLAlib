import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Chebyshev polynomials: growth outside `[-1, 1]` and the second kind

Facts about Mathlib's `Polynomial.Chebyshev.T ℝ q` and `U ℝ q` used by Krylov, Lanczos and
conjugate-gradient arguments.

* Growth for `x ≥ 1` (atlas `chebyshev-growth`): the closed form
  `T_q(x) = ((x + √(x² − 1))^q + (x − √(x² − 1))^q)/2`, the two-sided bound
  `(x + √(x² − 1))^q / 2 ≤ T_q(x) ≤ (x + √(x² − 1))^q`, monotonicity on `[1, ∞)`, the gap form
  `(1 + √(2γ))^q / 2 ≤ T_q(1 + γ)` and the condition-number form
  `((√b + √a)/(√b − √a))^q / 2 ≤ T_q((b + a)/(b − a))`.
* Second kind and derivatives on `[-1, 1]` (atlas `chebyshev-second-kind`):
  `|U_q(x)| ≤ q + 1`, `|T_q'(x)| ≤ q²`, and `T_q'(1) = q²`.

Atlas: `chebyshev-growth`, `chebyshev-second-kind`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Real

namespace NLAlib

/-! ### Growth for `x ≥ 1` -/

/-- Closed form of `T_q` on `[1, ∞)`: for `1 ≤ x`,
`T_q(x) = ((x + √(x² − 1))^q + (x − √(x² − 1))^q)/2`.
Source: Rivlin, *Chebyshev Polynomials* (1990), Eq. (1.49); Musco–Musco (2015) [`mm15`], proof
of Lem. 4. Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem eval_T_real_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ q).eval x = ((x + √(x ^ 2 - 1)) ^ q + (x - √(x ^ 2 - 1)) ^ q) / 2 := by
  have hs : 0 < x + √(x ^ 2 - 1) := by positivity
  have h := T_real_cosh (arcosh x) (q : ℤ)
  rw [cosh_arcosh hx] at h
  rw [h, arcosh, ← add_sqrt_self_sq_sub_one_inv hx, Int.cast_natCast, ← Real.log_pow,
    cosh_log (pow_pos hs q), inv_pow]

/-- Lower bound on the growth of `T_q` on `[1, ∞)`: for `1 ≤ x`,
`(x + √(x² − 1))^q / 2 ≤ T_q(x)`.
Source: Musco–Musco (2015) [`mm15`], proof of Lem. 4; Rivlin (1990), §1.5. Atlas:
`chebyshev-growth`.
atlas: chebyshev-growth -/
theorem pow_div_two_le_eval_T_real {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (x + √(x ^ 2 - 1)) ^ q / 2 ≤ (T ℝ q).eval x := by
  rw [eval_T_real_eq_of_one_le hx]
  have : 0 ≤ x - √(x ^ 2 - 1) := by
    rw [← add_sqrt_self_sq_sub_one_inv hx]; positivity
  have := pow_nonneg this q
  linarith

/-- Upper bound on the growth of `T_q` on `[1, ∞)`: for `1 ≤ x`, `T_q(x) ≤ (x + √(x² − 1))^q`.
Source: Rivlin (1990), §1.5. Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem eval_T_real_le_pow {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ q).eval x ≤ (x + √(x ^ 2 - 1)) ^ q := by
  rw [eval_T_real_eq_of_one_le hx]
  have h1 : 1 ≤ x + √(x ^ 2 - 1) := by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  have h0 : 0 ≤ x - √(x ^ 2 - 1) := by
    rw [← add_sqrt_self_sq_sub_one_inv hx]; positivity
  have h2 : x - √(x ^ 2 - 1) ≤ x + √(x ^ 2 - 1) := by
    have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  have := pow_le_pow_left₀ h0 h2 q
  linarith

/-- `T_q` is monotone on `[1, ∞)`.
Source: Rivlin (1990), §1.5 (from `T_q(cosh θ) = cosh(qθ)`). Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem monotoneOn_eval_T_real (q : ℕ) :
    MonotoneOn (fun x => (T ℝ q).eval x) (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  simp only
  rw [← cosh_arcosh hx, ← cosh_arcosh hy, T_real_cosh, T_real_cosh, cosh_le_cosh]
  have ha : arcosh x ≤ arcosh y := (arcosh_le_arcosh (by linarith) (by linarith)).2 hxy
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (by
    rw [abs_of_nonneg (arcosh_nonneg hx), abs_of_nonneg (arcosh_nonneg hy)]; exact ha)
    (abs_nonneg _)

/-- Gap form of the Chebyshev growth bound: for `0 ≤ γ`, `(1 + √(2γ))^q / 2 ≤ T_q(1 + γ)`.
Source: Musco–Musco (2015) [`mm15`], proof of Lem. 4. Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem one_add_sqrt_two_mul_pow_div_two_le_eval_T_real {γ : ℝ} (hγ : 0 ≤ γ) (q : ℕ) :
    (1 + √(2 * γ)) ^ q / 2 ≤ (T ℝ q).eval (1 + γ) := by
  refine le_trans ?_ (pow_div_two_le_eval_T_real (by linarith) q)
  have hs : √(2 * γ) ≤ √((1 + γ) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have : 1 + √(2 * γ) ≤ 1 + γ + √((1 + γ) ^ 2 - 1) := by linarith
  have := pow_le_pow_left₀ (by positivity) this q
  linarith

/-- The identity behind the condition-number form of the Chebyshev growth bound: for
`0 < a < b`, `(b + a)/(b − a) + √(((b + a)/(b − a))² − 1) = (√b + √a)/(√b − √a)`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 8; Saad, *Iterative Methods for Sparse Linear
Systems* (2003), §6.11.3. Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem add_div_sub_add_sqrt_sq_sub_one_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b + a) / (b - a) + √(((b + a) / (b - a)) ^ 2 - 1) = (√b + √a) / (√b - √a) := by
  have key : ∀ s t : ℝ, 0 < s → s < t →
      (t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2) + √(((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1) =
        (t + s) / (t - s) := by
    intro s t hs hst
    have hd : 0 < t ^ 2 - s ^ 2 := by nlinarith
    have hts : 0 < t - s := by linarith
    have hsq : ((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1 = (2 * t * s / (t ^ 2 - s ^ 2)) ^ 2 := by
      field_simp; ring
    have ht : 0 < t := by linarith
    rw [hsq, Real.sqrt_sq (div_nonneg (by positivity) hd.le)]
    field_simp
    ring
  have h := key (√a) (√b) (Real.sqrt_pos.2 ha) (Real.sqrt_lt_sqrt ha.le hab)
  rwa [Real.sq_sqrt ha.le, Real.sq_sqrt (by linarith)] at h

/-- Condition-number form of the Chebyshev growth bound: for `0 < a < b`,
`((√b + √a)/(√b − √a))^q / 2 ≤ T_q((b + a)/(b − a))`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 8; Saad (2003), §6.11.3. Atlas: `chebyshev-growth`.
atlas: chebyshev-growth -/
theorem sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (q : ℕ) :
    ((√b + √a) / (√b - √a)) ^ q / 2 ≤ (T ℝ q).eval ((b + a) / (b - a)) := by
  rw [← add_div_sub_add_sqrt_sq_sub_one_eq ha hab]
  exact pow_div_two_le_eval_T_real (by rw [le_div_iff₀ (by linarith)]; linarith) q

/-! ### Second kind and derivatives on `[-1, 1]` -/

/-- The derivative of `T_q` at `1` is `q²`.
Source: Rivlin (1990), §1.5; Mathlib `T_derivative_eq_U` and `U_eval_one`. Atlas:
`chebyshev-second-kind`.
atlas: chebyshev-second-kind -/
theorem eval_derivative_T_real_one (q : ℕ) : (derivative (T ℝ q)).eval 1 = (q : ℝ) ^ 2 := by
  rw [T_derivative_eq_U, eval_mul, U_eval_one]
  simp; ring

/-- The Chebyshev polynomial of the second kind is bounded by `q + 1` on `[-1, 1]`:
`|x| ≤ 1 → |U_q(x)| ≤ q + 1`.
Source: Rivlin (1990), §1.5. Atlas: `chebyshev-second-kind`. Proof: `T_{q+1}' = (q + 1) U_q`
and Mathlib's `abs_iterate_derivative_T_real_le` with one derivative.
atlas: chebyshev-second-kind -/
theorem abs_eval_U_real_le {x : ℝ} (hx : |x| ≤ 1) (q : ℕ) :
    |(U ℝ q).eval x| ≤ q + 1 := by
  have h := abs_iterate_derivative_T_real_le ((q : ℤ) + 1) 1 hx
  simp only [Function.iterate_one, T_derivative_eq_U, eval_mul, add_sub_cancel_right,
    U_eval_one] at h
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, eval_add, eval_natCast, eval_one]
    at h
  rw [abs_mul, abs_of_pos hq] at h
  exact le_of_mul_le_mul_left (by linarith) hq

/-- The derivative of `T_q` is bounded by `q²` on `[-1, 1]`: `|x| ≤ 1 → |T_q'(x)| ≤ q²`.
Source: Rivlin (1990), §1.5 (the case `p = T_q` of Markov's inequality). Atlas:
`chebyshev-second-kind`.
atlas: chebyshev-second-kind -/
theorem abs_eval_derivative_T_real_le {x : ℝ} (hx : |x| ≤ 1) (q : ℕ) :
    |(derivative (T ℝ q)).eval x| ≤ (q : ℝ) ^ 2 := by
  have h := abs_iterate_derivative_T_real_le (q : ℤ) 1 hx
  simp only [Function.iterate_one] at h
  rwa [eval_derivative_T_real_one] at h

end NLAlib

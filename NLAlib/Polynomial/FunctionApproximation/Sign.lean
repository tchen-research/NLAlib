import NLAlib.Polynomial.FunctionApproximation.HalfPlane
import Mathlib.Data.Real.Sign

/-!
# Polynomial sign filters away from zero

Approximate the inverse square root on `[γ²,1]`, then fold via `xq(x²)`.
Realises `sign-polynomial-approx`, with the explicit degree and error constants.
-/

noncomputable section

open Polynomial Set Real

namespace NLAlib

/-- Sign equals `x` times the inverse square root of `x²` away from zero.
Source: elementary real arithmetic; operator derivations §6,
helper for `sign-polynomial-approx`. -/
theorem sign_eq_mul_sq_rpow_neg_half {x : ℝ} (hx : x ≠ 0) :
    Real.sign x = x * (x ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg (sq_nonneg x), ← sqrt_eq_rpow, sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    field_simp
  · rw [Real.sign_of_pos h, abs_of_pos h, mul_inv_cancel₀ hx]

/-- Inverse-square-root approximation provides the exact Bernstein-ellipse sign filter.
Source: Trefethen, ATAP, Thm 8.2; operator derivations §6.
atlas: sign-polynomial-approx -/
theorem exists_sign_polynomial_of_bernstein_radius {γ ρ : ℝ} (hγ : 0 < γ)
    (hγone : γ < 1) (hρ : 1 < ρ) (hr : ρ < (1 + γ) / (1 - γ)) (n : ℕ) :
    ∃ q : ℝ[X], q.degree ≤ n ∧
      (X * q.comp (X ^ 2)).degree ≤ ((2 * n + 1 : ℕ) : WithBot ℕ) ∧
      ∀ x : ℝ, γ ≤ |x| → |x| ≤ 1 →
        |Real.sign x - (X * q.comp (X ^ 2)).eval x| ≤
          2 * (bernsteinIntervalLower (γ ^ 2) 1 ρ) ^ (-(1 / 2 : ℝ)) / ρ ^ n / (ρ - 1) := by
  have hγ2 : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hγ2one : γ ^ 2 < 1 := by nlinarith
  have hrad : ρ < (√(1 : ℝ) + √(γ ^ 2)) / (√(1 : ℝ) - √(γ ^ 2)) := by
    simpa only [sqrt_one, sqrt_sq hγ.le, add_comm] using hr
  have hm := bernsteinIntervalLower_pos hγ2 hγ2one hρ hrad
  have hml : bernsteinIntervalLower (γ ^ 2) 1 ρ ≤ bernsteinIntervalUpper (γ ^ 2) 1 ρ := by
    have hs : 0 ≤ ρ + ρ⁻¹ := by positivity
    dsimp [bernsteinIntervalLower, bernsteinIntervalUpper]
    nlinarith [mul_nonneg (sub_pos.mpr hγ2one).le hs]
  obtain ⟨q, hq, hE⟩ := exists_degree_le_abs_rpow_sub_eval_le
    hγ2 hγ2one hρ hrad (-(1 / 2 : ℝ)) n
  have hmax : max ((bernsteinIntervalLower (γ ^ 2) 1 ρ) ^ (-(1 / 2 : ℝ)))
      ((bernsteinIntervalUpper (γ ^ 2) 1 ρ) ^ (-(1 / 2 : ℝ))) =
      (bernsteinIntervalLower (γ ^ 2) 1 ρ) ^ (-(1 / 2 : ℝ)) :=
    max_eq_left (Real.rpow_le_rpow_of_nonpos hm hml (by norm_num))
  rw [hmax] at hE
  refine ⟨q, hq, ?_, ?_⟩
  · apply degree_le_of_natDegree_le
    have hqn := natDegree_le_of_degree_le hq
    have hcomp : (q.comp (X ^ 2)).natDegree ≤ 2 * n := by
      refine natDegree_comp_le.trans ?_
      simp only [natDegree_X_pow]
      omega
    exact natDegree_mul_le.trans (by simp only [natDegree_X]; omega)
  · intro x hxlo hxhi
    have hx0 : x ≠ 0 := by intro hx0; simpa [hx0] using hγ.trans_le hxlo
    have hx2 : x ^ 2 ∈ Icc (γ ^ 2) 1 := by
      rw [Set.mem_Icc]
      constructor <;> nlinarith [sq_abs x, abs_nonneg x]
    have hbound := hE (x ^ 2) hx2
    rw [sign_eq_mul_sq_rpow_neg_half hx0, eval_mul, eval_X, eval_comp, eval_pow,
      eval_X, ← mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg x)).trans
      (mul_le_of_le_one_left (by positivity) hxhi)

/-- At radius `1+γ`, the positive ellipse margin is exactly `γ²(3+γ)/4`.
Source: operator derivations §6; helper for `sign-polynomial-approx`. -/
theorem bernsteinIntervalLower_sq_one_add {γ : ℝ} (hγ : 0 < γ) :
    bernsteinIntervalLower (γ ^ 2) 1 (1 + γ) = γ ^ 2 * (3 + γ) / 4 := by
  dsimp [bernsteinIntervalLower]
  field_simp
  ring

/-- The elementary radius `1+γ` gives a sign polynomial with error
`4/(√3 γ²) (1+γ)⁻ⁿ` and degree at most `2n+1`.
Source: operator derivations §6; Trefethen, ATAP, Thm 8.2 applied to the inverse square root.
atlas: sign-polynomial-approx -/
theorem exists_sign_polynomial_abs_sub_eval_le {γ : ℝ} (hγ : 0 < γ)
    (hγone : γ < 1) (n : ℕ) :
    ∃ q : ℝ[X], q.degree ≤ n ∧
      (X * q.comp (X ^ 2)).degree ≤ ((2 * n + 1 : ℕ) : WithBot ℕ) ∧
      ∀ x : ℝ, γ ≤ |x| → |x| ≤ 1 →
        |Real.sign x - (X * q.comp (X ^ 2)).eval x| ≤
          (4 / (√3 * γ ^ 2)) / (1 + γ) ^ n := by
  have hr : 1 + γ < (1 + γ) / (1 - γ) := by
    rw [lt_div_iff₀ (sub_pos.mpr hγone)]
    nlinarith
  obtain ⟨q, hq, hd, hE⟩ := exists_sign_polynomial_of_bernstein_radius
    hγ hγone (by linarith) hr n
  have hm : 0 < bernsteinIntervalLower (γ ^ 2) 1 (1 + γ) := by
    rw [bernsteinIntervalLower_sq_one_add hγ]
    positivity
  have hs : √3 * γ / 2 ≤ √(bernsteinIntervalLower (γ ^ 2) 1 (1 + γ)) := by
    have hs3 : √(3 : ℝ) ^ 2 = 3 := sq_sqrt (by norm_num)
    have hsm := sq_sqrt hm.le
    rw [bernsteinIntervalLower_sq_one_add hγ] at hsm ⊢
    nlinarith [sqrt_nonneg (3 : ℝ), sqrt_nonneg (γ ^ 2 * (3 + γ) / 4)]
  have hspos : 0 < √(bernsteinIntervalLower (γ ^ 2) 1 (1 + γ)) := sqrt_pos.mpr hm
  have hs3pos : 0 < √(3 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hconst : 2 / √(bernsteinIntervalLower (γ ^ 2) 1 (1 + γ)) / γ ≤ 4 / (√3 * γ ^ 2) := by
    rw [div_div, div_le_div_iff₀ (mul_pos hspos hγ) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs hγ.le]
  refine ⟨q, hq, hd, fun x hxlo hxhi => (hE x hxlo hxhi).trans ?_⟩
  have heq : 2 * (bernsteinIntervalLower (γ ^ 2) 1 (1 + γ)) ^ (-(1 / 2 : ℝ)) /
      (1 + γ) ^ n / ((1 + γ) - 1) =
      (2 / √(bernsteinIntervalLower (γ ^ 2) 1 (1 + γ)) / γ) / (1 + γ) ^ n := by
    rw [rpow_neg hm.le, ← sqrt_eq_rpow]
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right hconst (by positivity)

end NLAlib

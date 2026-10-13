import NLAlib.Polynomial.FunctionApproximation.AbsoluteChebyshevSeries
import Mathlib.Data.Real.Sign
import NLAlib.ForMathlib.Analysis.OddSineSeries

/-!
# Explicit Chebyshev coefficients of the sign function

The real sign function has value zero at zero. Ordinary cosine integrals determine
its exact alternating odd Chebyshev coefficients and vanishing even coefficients.
Atlas: `chebyshev-series-abs-sign`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set Filter MeasureTheory
open scoped Topology

namespace NLAlib

/-- Reflection reduces the sign-function coefficient integral to the positive half period.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`.
Endpoint values and the value at the central jump do not affect the integral. -/
theorem chebyshevCoeff_sign_eq_half_integral (k : ℕ) :
    chebyshevCoeff Real.sign k = (if k = 0 then 1 else 2) / Real.pi * (1 - (-1 : ℝ) ^ k) *
      ∫ θ in 0..Real.pi / 2, Real.cos ((k : ℝ) * θ) := by
  let u : ℝ → ℝ := fun θ => Real.sign (Real.cos θ) * Real.cos ((k : ℝ) * θ)
  have hfirst : EqOn u (fun θ => Real.cos ((k : ℝ) * θ)) (uIoo 0 (Real.pi / 2)) := by
    intro θ hθ
    have ht : θ ∈ Ioo 0 (Real.pi / 2) := by simpa [uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
    dsimp only [u]
    rw [Real.sign_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩), one_mul]
  have hsecond : EqOn u (fun θ => -Real.cos ((k : ℝ) * θ)) (uIoo (Real.pi / 2) Real.pi) := by
    intro θ hθ
    have ht : θ ∈ Ioo (Real.pi / 2) Real.pi := by
      simpa [uIoo_of_le (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos])] using hθ
    dsimp only [u]
    have hneg : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
      ht.1 (by linarith [ht.2, Real.pi_pos])
    rw [Real.sign_of_neg hneg, neg_one_mul]
  have hi1 : IntervalIntegrable u volume 0 (Real.pi / 2) :=
    ((by fun_prop : Continuous (fun θ : ℝ => Real.cos ((k : ℝ) * θ))).intervalIntegrable _ _).congr_uIoo hfirst.symm
  have hi2 : IntervalIntegrable u volume (Real.pi / 2) Real.pi :=
    ((by fun_prop : Continuous (fun θ : ℝ => -Real.cos ((k : ℝ) * θ))).intervalIntegrable _ _).congr_uIoo hsecond.symm
  have hsym : ∀ θ, u (Real.pi - θ) = -((-1 : ℝ) ^ k) * u θ := by
    intro θ
    dsimp only [u]
    rw [Real.cos_pi_sub, Real.sign_neg,
      show (k : ℝ) * (Real.pi - θ) = (k : ℝ) * Real.pi - (k : ℝ) * θ by ring,
      Real.cos_nat_mul_pi_sub]
    ring
  have hreflect : (∫ θ in Real.pi / 2..Real.pi, u θ) =
      -((-1 : ℝ) ^ k) * ∫ θ in 0..Real.pi / 2, u θ := by
    have h := intervalIntegral.integral_comp_sub_left (f := u) (a := 0) (b := Real.pi / 2) Real.pi
    simp only [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero, hsym] at h
    rw [intervalIntegral.integral_const_mul] at h
    exact h.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [chebyshevCoeff_eq_cosine_integral]
  change (if k = 0 then 1 else 2) / Real.pi * (∫ θ in 0..Real.pi, u θ) = _
  rw [← hsplit, hreflect, intervalIntegral.integral_congr_uIoo hfirst]
  ring

/-- Every even Chebyshev coefficient of the real sign function vanishes.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
@[simp] theorem chebyshevCoeff_sign_even (j : ℕ) : chebyshevCoeff Real.sign (2 * j) = 0 := by
  rw [chebyshevCoeff_sign_eq_half_integral]
  simp [pow_mul]

/-- The exact odd sign coefficients have the corrected alternating sign `(-1)^j`.
Source: Trefethen, ATAP, Exercise 3.6; the coefficient at frequency `2j+1` is `4(-1)^j/(π(2j+1))`.
atlas: chebyshev-series-abs-sign (partial) -/
theorem chebyshevCoeff_sign_odd (j : ℕ) :
    chebyshevCoeff Real.sign (2 * j + 1) = 4 * (-1 : ℝ) ^ j / (Real.pi * (2 * j + 1)) := by
  rw [chebyshevCoeff_sign_eq_half_integral, if_neg (by omega),
    integral_cos_mul_half_pi _ (by positivity)]
  have hsin : Real.sin (((2 * j + 1 : ℕ) : ℝ) * (Real.pi / 2)) = (-1 : ℝ) ^ j := by
    rw [show (((2 * j + 1 : ℕ) : ℝ)) * (Real.pi / 2) = (j : ℝ) * Real.pi + Real.pi / 2 by push_cast; ring]
    simp [Real.sin_add, Real.cos_nat_mul_pi]
  rw [hsin]
  simp [pow_add, pow_mul]
  field_simp
  ring

/-- Odd Chebyshev polynomials at a sine argument become odd sine frequencies after alternation.
Source: the Chebyshev cosine identity; helper for `chebyshev-series-abs-sign`. -/
theorem neg_one_pow_mul_eval_T_odd_sin (j : ℕ) (φ : ℝ) :
    (-1 : ℝ) ^ j * (T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval (Real.sin φ) =
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) := by
  rw [← Real.cos_pi_div_two_sub φ, T_real_cos]
  have hangle : ((2 * j + 1 : ℕ) : ℝ) * (Real.pi / 2 - φ) =
      (Real.pi / 2 - ((2 * j + 1 : ℕ) : ℝ) * φ) + (j : ℝ) * Real.pi := by
    push_cast
    ring
  simp only [Int.cast_natCast]
  rw [hangle, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two_sub,
    ← mul_assoc, ← mul_pow]
  norm_num

/-- The sign Chebyshev series converges in its ordinary partial-sum order at every point
of `[-1,1]`, with value zero at the jump. Away from the jump the value follows from
the proved odd-sine Dirichlet/Abel theorem, not absolute summability.
Source: Trefethen, ATAP, Exercise 3.6; operator rederivations `polyseries:abs-sign`.
Together with the exact absolute-value tail and both coefficient formulas, this realizes
the original absolute-value/sign series item.
atlas: chebyshev-series-abs-sign -/
theorem tendsto_sum_sign_chebyshevSeries {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun m => 4 / Real.pi * ∑ j ∈ range m,
      ((-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) * (T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x)
      atTop (𝓝 (Real.sign x)) := by
  by_cases hx0 : x = 0
  · subst x
    have hterm : ∀ j : ℕ, ((-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) *
        (T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval 0 = 0 := by
      intro j
      have h := neg_one_pow_mul_eval_T_odd_sin j 0
      simp only [Real.sin_zero, mul_zero] at h
      rw [div_mul_eq_mul_div, h, zero_div]
    simp_rw [hterm, sum_const_zero, mul_zero, Real.sign_zero]
    exact tendsto_const_nhds
  · have hsin : Real.sin (Real.arcsin x) = x := Real.sin_arcsin hx.1 hx.2
    have h := (tendsto_sum_sin_odd_div (Real.arcsin x) (by rwa [hsin])).const_mul (4 / Real.pi)
    have hvalue : 4 / Real.pi * (Real.pi / 4 * Real.sign (Real.sin (Real.arcsin x))) = Real.sign x := by
      rw [hsin]
      field_simp
    rw [hvalue] at h
    have hfunc : (fun m => 4 / Real.pi * ∑ j ∈ range m,
        ((-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) * (T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x) =
        fun m => 4 / Real.pi * ∑ j ∈ range m,
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.arcsin x) / (2 * (j : ℝ) + 1) := by
      funext m
      congr 1
      apply sum_congr rfl
      intro j hj
      have hT := neg_one_pow_mul_eval_T_odd_sin j (Real.arcsin x)
      rw [hsin] at hT
      rw [div_mul_eq_mul_div, hT]
    rw [hfunc]
    exact h

end NLAlib

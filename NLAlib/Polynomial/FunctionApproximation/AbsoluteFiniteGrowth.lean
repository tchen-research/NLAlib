import NLAlib.Polynomial.FunctionApproximation.AbsoluteChebyshevSeries
import NLAlib.Polynomial.FunctionApproximation.SineCoordinates
import NLAlib.ForMathlib.Analysis.Complex.TrigonometricGrowth
import Mathlib.Tactic.FieldSimp

/-!
# Finite complex growth for absolute-value comparison polynomials

The actual absolute-value Chebyshev truncation has a finite expression in sine
coordinates with a quadratic complex growth bound. This is the comparison
polynomial in the focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Complex

namespace NLAlib

/-- Even-order Chebyshev polynomials evaluated at a complex sine coordinate have
the signed cosine multiple-angle value. -/
theorem eval_T_even_sin (j : ℕ) (u : ℂ) :
    (T ℂ (2 * j : ℕ)).eval (Complex.sin u) =
      (-1 : ℂ)^j * Complex.cos (2 * (j : ℂ) * u) := by
  rw [← Complex.cos_pi_div_two_sub, T_complex_cos]
  simp only [Int.cast_natCast]
  have he : ((2 * j : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 - u) =
      ((j * Real.pi : ℝ) : ℂ) - 2 * (j : ℂ) * u := by push_cast; ring
  rw [he, Complex.cos_sub, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  simp

private theorem chebyshevTrunc_abs_succ_even (m : ℕ) :
    chebyshevTrunc (fun x : ℝ => |x|) (2 * (m + 1)) =
      chebyshevTrunc (fun x : ℝ => |x|) (2 * m) +
        C (chebyshevCoeff (fun x : ℝ => |x|) (2 * (m + 1))) *
          T ℝ (2 * (m + 1) : ℕ) := by
  unfold chebyshevTrunc
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
    sum_range_succ, sum_range_succ, chebyshevCoeff_abs_odd]
  simp only [C_0, zero_mul, add_zero]
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]

/-- The actual absolute-value Chebyshev truncation has a cancellation-preserving
finite expression in a complex sine coordinate. -/
theorem eval_chebyshevTrunc_abs_even_sin (m : ℕ) (u : ℂ) :
    ((chebyshevTrunc (fun x : ℝ => |x|) (2 * m)).map Complex.ofRealHom).eval
      (Complex.sin u) =
      (2 / (Real.pi * (2 * m + 1)) : ℝ) +
        (4 / Real.pi : ℝ) * ∑ j ∈ range m,
          (1 - Complex.cos (2 * ((j + 1 : ℕ) : ℂ) * u)) /
            (4 * ((j + 1 : ℕ) : ℂ)^2 - 1) := by
  induction m with
  | zero => simp [chebyshevTrunc]
  | succ m ih =>
    rw [chebyshevTrunc_abs_succ_even, Polynomial.map_add, eval_add, ih,
      Polynomial.map_mul, Polynomial.map_C, map_T, eval_mul, eval_C,
      chebyshevCoeff_abs_even (by omega), eval_T_even_sin, sum_range_succ]
    have hsign : (-1 : ℂ)^(m + 1 + 1) * (-1 : ℂ)^(m + 1) = -1 := by
      rw [pow_succ, mul_right_comm, ← mul_pow]
      norm_num
    have hd : 4 * ((m + 1 : ℕ) : ℂ)^2 - 1 ≠ 0 := by
      have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
      have h : (4 * ((m + 1 : ℕ) : ℝ)^2 - 1) ≠ 0 := by nlinarith
      exact_mod_cast h
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hd0 : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
    have hd1 : ((2 * (m + 1) + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show 2 * (m + 1) + 1 ≠ 0 by omega)
    have hterm : Complex.ofRealHom (4 / Real.pi * (-1 : ℝ)^(m + 1 + 1) /
        (4 * ((m + 1 : ℕ) : ℝ)^2 - 1)) *
          ((-1 : ℂ)^(m + 1) * Complex.cos (2 * ((m + 1 : ℕ) : ℂ) * u)) =
        -(4 / (Real.pi : ℂ)) * Complex.cos (2 * ((m + 1 : ℕ) : ℂ) * u) /
          (4 * ((m + 1 : ℕ) : ℂ)^2 - 1) := by
      set H := Complex.cos (2 * ((m + 1 : ℕ) : ℂ) * u)
      simp only [Complex.ofRealHom_eq_coe]
      push_cast
      linear_combination 4 / (Real.pi : ℂ) * H /
        (4 * ((m : ℂ) + 1)^2 - 1) * hsign
    rw [hterm]
    set S : ℂ := ∑ j ∈ range m,
      (1 - Complex.cos (2 * ((j + 1 : ℕ) : ℂ) * u)) /
        (4 * ((j + 1 : ℕ) : ℂ)^2 - 1)
    push_cast
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hd hd0 hd1
    field_simp [hπ, hd, hd0, hd1]
    ring

/-- The finite absolute-value comparison polynomial has a quadratic complex
growth bound in a sine coordinate, uniform in the order of each summand. -/
theorem norm_eval_chebyshevTrunc_abs_even_sin_le (m : ℕ) (u : ℂ) :
    ‖((chebyshevTrunc (fun x : ℝ => |x|) (2 * m)).map Complex.ofRealHom).eval
      (Complex.sin u)‖ ≤
      2 / (Real.pi * (2 * m + 1)) +
        8 * m / (3 * Real.pi) * ‖u‖^2 * Real.exp ((2 * m : ℕ) * |u.im|) := by
  have hterm (j : ℕ) (hj : j ∈ range m) :
      ‖(1 - Complex.cos (2 * ((j + 1 : ℕ) : ℂ) * u)) /
          (4 * ((j + 1 : ℕ) : ℂ)^2 - 1)‖ ≤
        (2 / 3 : ℝ) * ‖u‖^2 * Real.exp ((2 * m : ℕ) * |u.im|) := by
    have hjm : j + 1 ≤ m := by have := mem_range.mp hj; omega
    have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    have hd : 0 < 4 * ((j + 1 : ℕ) : ℝ)^2 - 1 := by nlinarith
    have hden : ‖(4 * ((j + 1 : ℕ) : ℂ)^2 - 1)‖ =
        4 * ((j + 1 : ℕ) : ℝ)^2 - 1 := by
      have he : 4 * ((j + 1 : ℕ) : ℂ)^2 - 1 =
          ((4 * ((j + 1 : ℕ) : ℝ)^2 - 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hn : ‖2 * ((j + 1 : ℕ) : ℂ) * u‖^2 / 2 =
        2 * ((j + 1 : ℕ) : ℝ)^2 * ‖u‖^2 := by
      rw [norm_mul, norm_mul, norm_ofNat, Complex.norm_natCast]
      ring
    have hi : |(2 * ((j + 1 : ℕ) : ℂ) * u).im| =
        2 * ((j + 1 : ℕ) : ℝ) * |u.im| := by
      norm_num [Complex.mul_im, Complex.mul_re, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
      exact Or.inl (by positivity)
    have harg : 2 * ((j + 1 : ℕ) : ℝ) * |u.im| ≤
        ((2 * m : ℕ) : ℝ) * |u.im| := by
      have h : ((j + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have hc := Complex.norm_one_sub_cos_le_norm_sq_mul_exp_abs_im
      (2 * ((j + 1 : ℕ) : ℂ) * u)
    rw [hn, hi] at hc
    have hc' := hc.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by positivity))
    have hratio : 2 * ((j + 1 : ℕ) : ℝ)^2 /
        (4 * ((j + 1 : ℕ) : ℝ)^2 - 1) ≤ 2 / 3 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    rw [norm_div, hden]
    refine (div_le_div_of_nonneg_right hc' hd.le).trans ?_
    have hbound := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ ‖u‖^2 * Real.exp ((2 * m : ℕ) * |u.im|) by positivity)
    convert hbound using 1 <;> ring
  have hs := (norm_sum_le (range m) _).trans (sum_le_sum hterm)
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  rw [eval_chebyshevTrunc_abs_even_sin]
  refine (norm_add_le _ _).trans ?_
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc0 : 0 ≤ 2 / (Real.pi * (2 * m + 1)) := by positivity
  have hc4 : 0 ≤ 4 / Real.pi := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc4]
  have hbound := mul_le_mul_of_nonneg_left hs hc4
  convert add_le_add_left hbound (2 / (Real.pi * (2 * m + 1))) using 1 <;> ring

end NLAlib

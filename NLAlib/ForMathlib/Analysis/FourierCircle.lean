import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Explicit Fourier characters on the circle of period two pi

Character multiplication in the argument, reflection, natural frequencies as powers of the
first character, the unit-circle parametrisation, uniform-grid roots of unity, and the
real-angle cosine and sine formulas are generic Fourier facts used by the sharp Jackson
square-wave duality and the analytic Chebyshev (Fourier) reconstruction.
The scoped instance `NLAlib.TwoPi.fact_zero_lt_two_pi` (`open scoped NLAlib.TwoPi`) supplies
the period fact `0 < 2π` to every file working on `AddCircle (2 * π)`.

Upstreaming note: `fourier_apply_add` (`fourier_apply` with `AddCircle.toCircle_add`),
`fourier_apply_neg` (`fourier_apply` with `smul_neg`) and `fourier_nat_eq_pow` (induction on
Mathlib's `fourier_add`) are short corollaries of Mathlib's `Mathlib/Analysis/Fourier/AddCircle`
API, stated for period `2π` only; candidates for upstreaming for a general period `T`.
-/

noncomputable section

open Complex
open scoped Real

namespace NLAlib

namespace TwoPi

/-- `0 < 2π` as a `Fact`, the period hypothesis Mathlib's `AddCircle (2 * π)` API (Haar
measure, Fourier characters) needs. Scoped rather than global, as in Mathlib's own local
instance (`Mathlib/Analysis/Polynomial/Fourier.lean`); activate it with
`open scoped NLAlib.TwoPi`. -/
scoped instance fact_zero_lt_two_pi : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

end TwoPi

open scoped TwoPi

/-- Fourier characters multiply under addition of their circle arguments.
Source: Mathlib's additive-circle Fourier definition; used by sharp `jackson-lipschitz`. -/
theorem fourier_apply_add (k : ℤ) (x y : AddCircle (2 * Real.pi)) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- A uniform `N`-grid step has the standard complex root-of-unity Fourier value.
Source: Mathlib's additive-circle Fourier definition; used by sharp `jackson-lipschitz`. -/
theorem fourier_nat_div_period (k N : ℕ) (hN : 0 < N) :
    fourier (k : ℤ) ((2 * Real.pi / N : ℝ) : AddCircle (2 * Real.pi)) =
      Complex.exp (2 * Real.pi * I * (k : ℂ) / (N : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- The `N`-th character is one at a uniform `N`-grid step.
Source: roots of unity; used by sharp `jackson-lipschitz`. -/
theorem fourier_nat_div_period_eq_one (N : ℕ) (hN : 0 < N) :
    fourier (N : ℤ) ((2 * Real.pi / N : ℝ) : AddCircle (2 * Real.pi)) = 1 := by
  rw [fourier_nat_div_period N N hN]
  exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hN.ne').mpr (dvd_refl N)

/-- A character with positive frequency below `N` is not one at a uniform `N`-grid step.
Source: roots of unity; used by sharp `jackson-lipschitz`. -/
theorem fourier_nat_div_period_ne_one {k N : ℕ} (hk : 0 < k) (hkN : k < N) :
    fourier (k : ℤ) ((2 * Real.pi / N : ℝ) : AddCircle (2 * Real.pi)) ≠ 1 := by
  intro hone
  rw [fourier_nat_div_period k N (hk.trans hkN)] at hone
  have hdvd := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (Nat.ne_of_gt (hk.trans hkN))).mp hone
  exact (Nat.le_of_dvd hk hdvd).not_gt hkN

/-- The real part of a period-`2π` Fourier monomial is the usual cosine frequency.
Source: Trefethen, ATAP, Chapters 3 and 8; used by analytic Chebyshev approximation
and sharp Jackson. Relocated unchanged from `NLAlib.Polynomial.FunctionApproximation.AnalyticApproximation`. -/
theorem re_fourier_nat_coe_eq_cos (k : ℕ) (θ : ℝ) :
    (fourier (k : ℤ) (θ : AddCircle (2 * Real.pi))).re = Real.cos ((k : ℝ) * θ) := by
  rw [fourier_coe_apply]
  push_cast
  have heq : 2 * (Real.pi : ℂ) * I * (k : ℂ) * (θ : ℂ) / (2 * Real.pi) =
      (((k : ℝ) * θ : ℝ) : ℂ) * I := by
    push_cast
    field_simp
  rw [heq]
  rw [Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The imaginary part of the natural Fourier character at a real angle is its sine.
Source: Mathlib's additive-circle Fourier definition; used by sharp `jackson-lipschitz`. -/
theorem im_fourier_nat_coe_eq_sin (k : ℕ) (t : ℝ) :
    (fourier (k : ℤ) (t : AddCircle (2 * Real.pi))).im = Real.sin ((k : ℝ) * t) := by
  rw [fourier_coe_apply]
  push_cast
  have heq : 2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ) / (2 * Real.pi) =
      (((k : ℝ) * t : ℝ) : ℂ) * I := by
    push_cast
    field_simp
  rw [heq, Complex.exp_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

/-- Reflecting a Fourier monomial in the circle reverses its frequency.
Source: Mathlib additive-circle Fourier definition; helper for `chebyshev-approx-analytic`. -/
theorem fourier_apply_neg (k : ℤ) (θ : AddCircle (2 * Real.pi)) :
    fourier k (-θ) = fourier (-k) θ := by
  simp only [fourier_apply, smul_neg, neg_smul]

/-- Natural Fourier frequencies are powers of the first unit-circle monomial.
Source: Mathlib additive-circle Fourier multiplication; helper for `chebyshev-approx-analytic`. -/
theorem fourier_nat_eq_pow (k : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier (k : ℤ) θ = fourier 1 θ ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- Fourier monomials of period `2π` equal the unit-circle parametrization at frequency one.
Source: Mathlib additive-circle Fourier definition; helper for `chebyshev-approx-analytic`. -/
theorem fourier_one_eq_circleMap (θ : ℝ) :
    fourier 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_apply]
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
  congr 1
  push_cast
  field_simp

end NLAlib

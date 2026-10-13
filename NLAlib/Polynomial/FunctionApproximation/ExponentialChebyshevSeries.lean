import NLAlib.ForMathlib.Analysis.FourierSeries
import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential Chebyshev coefficients and modified Bessel series

Two scalar exponential power series and Fourier coefficient extraction give the
modified Bessel power series, with the exact integral normalization.
Atlas: `chebyshev-series-exp-bessel`.
-/

noncomputable section

set_option maxHeartbeats 600000

open Polynomial Polynomial.Chebyshev Finset Real Set MeasureTheory
open scoped Topology ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The exponential's Chebyshev coefficients are the modified Bessel coefficients,
with the constant coefficient undoubled.
Source: Trefethen, ATAP, Exercise 3.15.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem chebyshevCoeff_exp_eq_modifiedBesselCoeff (a : ℝ) (k : ℕ) :
    chebyshevCoeff (fun x => Real.exp (a * x)) k = (if k = 0 then 1 else 2) * modifiedBesselCoeff a k := by
  rw [chebyshevCoeff_eq_cosine_integral]
  unfold modifiedBesselCoeff
  ring

/-- A holomorphic exponential pulled back through the positive circle character.
Source: the exponential generating function; helper for `chebyshev-series-exp-bessel`. -/
def circleExponential (b : ℝ) (t : AddCircle (2 * Real.pi)) : ℂ :=
  Complex.exp ((b : ℂ) * fourier 1 t)

/-- Factorial coefficient norms form a summable majorant.
Source: scalar exponential power series; helper for `chebyshev-series-exp-bessel`. -/
theorem summable_abs_pow_div_factorial (b : ℝ) :
    Summable (fun n : ℕ => |b| ^ n / (n.factorial : ℝ)) := by
  have habs : ∀ n : ℕ, |(n.factorial : ℝ)| = (n.factorial : ℝ) :=
    fun n => abs_of_nonneg (Nat.cast_nonneg _)
  simpa only [Real.norm_eq_abs, abs_div, abs_pow, habs] using
    NormedSpace.norm_expSeries_div_summable b

/-- The positive-circle exponential has its genuine uniformly dominated character expansion.
Source: scalar exponential power series; helper for `chebyshev-series-exp-bessel`. -/
theorem hasSum_circleExponential (b : ℝ) (t : AddCircle (2 * Real.pi)) :
    HasSum (fun n : ℕ => ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * fourier (n : ℤ) t)
      (circleExponential b t) := by
  unfold circleExponential
  rw [Complex.exp_eq_exp_ℂ]
  have h := NormedSpace.expSeries_div_hasSum_exp ((b : ℂ) * fourier 1 t)
  have heq : (fun n : ℕ => ((b : ℂ) * fourier 1 t) ^ n / (n.factorial : ℂ)) =
      fun n : ℕ => ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * fourier (n : ℤ) t := by
    funext n
    rw [mul_pow, fourier_nat_eq_pow]
    push_cast
    ring
  rw [heq] at h
  exact h

/-- The positive-circle exponential is uniformly bounded by `exp |b|`.
Source: the norm of the complex exponential; helper for `chebyshev-series-exp-bessel`. -/
theorem norm_circleExponential_le (b : ℝ) (t : AddCircle (2 * Real.pi)) :
    ‖circleExponential b t‖ ≤ Real.exp |b| := by
  rw [circleExponential, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply Real.exp_le_exp.mpr
  calc b * (fourier 1 t).re ≤ |b * (fourier 1 t).re| := le_abs_self _
    _ = |b| * |(fourier 1 t).re| := abs_mul _ _
    _ ≤ |b| * 1 := mul_le_mul_of_nonneg_left
      (abs_le.mpr (re_fourier_one_mem_Icc t)) (abs_nonneg _)
    _ = |b| := mul_one _

/-- Positive Fourier coefficients of the positive-circle exponential are factorial monomials.
Source: termwise integration of its uniformly dominated power series;
helper for `chebyshev-series-exp-bessel`. -/
theorem fourierCoeff_circleExponential_nat (b : ℝ) (k : ℕ) :
    fourierCoeff (circleExponential b) (k : ℤ) = ((b ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
  let F : ℕ → AddCircle (2 * Real.pi) → ℂ := fun n t =>
    ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * fourier (n : ℤ) t
  have h := hasSum_fourierCoeff_of_summable_bound (F := F)
    (b := fun n => |b| ^ n / (n.factorial : ℝ))
    (fun n => continuous_const.mul (fourier (n : ℤ)).continuous)
    (summable_abs_pow_div_factorial b) (fun n t => by
      change ‖((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * fourier (n : ℤ) t‖ ≤ _
      rw [norm_mul, show ‖fourier (n : ℤ) t‖ = (1 : ℝ) from Circle.norm_coe _, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)] ) (hasSum_circleExponential b) (k : ℤ)
  have hterm : ∀ n, fourierCoeff (F n) (k : ℤ) =
      if n = k then ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) else 0 := by
    intro n
    change fourierCoeff (fun t => ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * fourier (n : ℤ) t) _ = _
    rw [fourierCoeff.const_mul]
    have hc := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) (n : ℤ)) (k : ℤ)
    rw [hc]
    by_cases hnk : n = k
    · subst n
      simp
    · have hkn : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast Ne.symm hnk
      simp only [Pi.single_apply, if_neg hnk, if_neg hkn, mul_zero]
  simp_rw [hterm] at h
  have hsingle : HasSum (fun n : ℕ =>
      if n = k then ((b ^ n / (n.factorial : ℝ) : ℝ) : ℂ) else 0)
      ((b ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
    convert hasSum_ite_eq k ((b ^ k / (k.factorial : ℝ) : ℝ) : ℂ) using 1
    funext n
    by_cases hn : n = k
    · subst n; simp
    · simp [hn]
  exact h.unique hsingle

/-- The actual Fourier coefficient of `exp(a cos θ)` has the modified Bessel power series.
Source: Trefethen, ATAP, Exercise 3.15; two scalar exponential power series.
Helper for `chebyshev-series-exp-bessel`. -/
theorem hasSum_pow_div_factorial_modifiedBesselCoeff (a : ℝ) (k : ℕ) :
    HasSum (fun j : ℕ => (a / 2) ^ (2 * j + k) /
      ((j.factorial : ℝ) * ((j + k).factorial : ℝ))) (modifiedBesselCoeff a k) := by
  let b : ℝ := a / 2
  let F : ℕ → AddCircle (2 * Real.pi) → ℂ := fun j t =>
    ((b ^ j / (j.factorial : ℝ) : ℝ) : ℂ) * fourier (-(j : ℤ)) t * circleExponential b t
  let f : AddCircle (2 * Real.pi) → ℂ := fun t => (Real.exp (a * (fourier 1 t).re) : ℂ)
  have hcont : Continuous (circleExponential b) := by unfold circleExponential; fun_prop
  have hseries : ∀ t, HasSum (fun j => F j t) (f t) := by
    intro t
    have h := (hasSum_circleExponential b (-t)).mul_right (circleExponential b t)
    simp only [fourier_apply_neg] at h
    have heq : circleExponential b (-t) * circleExponential b t = f t := by
      change Complex.exp ((b : ℂ) * fourier 1 (-t)) * Complex.exp ((b : ℂ) * fourier 1 t) =
        (Real.exp (a * (fourier 1 t).re) : ℂ)
      rw [← Complex.exp_add, Complex.ofReal_exp]
      apply congrArg Complex.exp
      rw [fourier_apply_neg, fourier_neg]
      apply Complex.ext
      · simp [b, Complex.mul_re]
        ring
      · simp [Complex.mul_im]
    rw [heq] at h
    exact h
  have hbound : ∀ j t, ‖F j t‖ ≤ (|b| ^ j / (j.factorial : ℝ)) * Real.exp |b| := by
    intro j t
    change ‖((b ^ j / (j.factorial : ℝ) : ℝ) : ℂ) * fourier (-(j : ℤ)) t * circleExponential b t‖ ≤ _
    rw [norm_mul, norm_mul, show ‖fourier (-(j : ℤ)) t‖ = (1 : ℝ) from Circle.norm_coe _,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ j.factorial by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_circleExponential_le b t) (by positivity)
  have hs := hasSum_fourierCoeff_of_summable_bound (F := F)
    (b := fun j => (|b| ^ j / (j.factorial : ℝ)) * Real.exp |b|)
    (fun j => (continuous_const.mul (fourier (-(j : ℤ))).continuous).mul hcont)
    ((summable_abs_pow_div_factorial b).mul_right _) hbound hseries (k : ℤ)
  have hterm : ∀ j, fourierCoeff (F j) (k : ℤ) =
      (((a / 2) ^ (2 * j + k) / ((j.factorial : ℝ) * ((j + k).factorial : ℝ)) : ℝ) : ℂ) := by
    intro j
    have heq : F j = fun t => ((b ^ j / (j.factorial : ℝ) : ℝ) : ℂ) *
        (fourier (-(j : ℤ)) t * circleExponential b t) := by
      funext t
      change (_ * _) * _ = _ * (_ * _)
      exact mul_assoc _ _ _
    rw [heq, fourierCoeff.const_mul, fourierCoeff_fourier_mul]
    have hidx : (k : ℤ) - -(j : ℤ) = ((j + k : ℕ) : ℤ) := by omega
    rw [hidx, fourierCoeff_circleExponential_nat]
    push_cast
    rw [div_mul_div_comm, ← pow_add]
    have he : j + (j + k) = 2 * j + k := by omega
    rw [he]
    dsimp only [b]
    push_cast
    ring
  simp_rw [hterm] at hs
  have hr := Complex.reCLM.hasSum hs
  change HasSum (fun j : ℕ =>
    ((((a / 2) ^ (2 * j + k) / ((j.factorial : ℝ) * ((j + k).factorial : ℝ)) : ℝ) : ℂ)).re)
      (fourierCoeff f (k : ℤ)).re at hr
  have hcoeff : (fourierCoeff f (k : ℤ)).re = modifiedBesselCoeff a k := by
    have h := re_fourierCoeff_realChebyshevCircleFunction
      (f := fun x => Real.exp (a * x)) (by fun_prop) k
    exact h
  rw [hcoeff] at hr
  simpa only [Complex.ofReal_re] using hr

/-- Modified Bessel coefficients are nonnegative for nonnegative arguments.
Source: Trefethen, ATAP, Exercise 3.15; the genuine factorial power series.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem modifiedBesselCoeff_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ modifiedBesselCoeff a k := by
  rw [← (hasSum_pow_div_factorial_modifiedBesselCoeff a k).tsum_eq]
  apply tsum_nonneg
  intro j
  positivity

/-- The sharp elementary factorial bound on nonnegative modified Bessel coefficients.
Source: Trefethen, ATAP, Exercise 3.15; `(j+k)! ≥ k!` in the genuine power series.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem modifiedBesselCoeff_le_pow_div_factorial_mul_exp {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    modifiedBesselCoeff a k ≤ (a / 2) ^ k / (k.factorial : ℝ) * Real.exp (a ^ 2 / 4) := by
  let b : ℝ := a / 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs := hasSum_pow_div_factorial_modifiedBesselCoeff a k
  have he : HasSum (fun j : ℕ => (b ^ 2) ^ j / (j.factorial : ℝ)) (Real.exp (b ^ 2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (b ^ 2)
  have hm := he.mul_left (b ^ k / (k.factorial : ℝ))
  have hterm : ∀ j : ℕ, (a / 2) ^ (2 * j + k) /
      ((j.factorial : ℝ) * ((j + k).factorial : ℝ)) ≤
        (b ^ k / (k.factorial : ℝ)) * ((b ^ 2) ^ j / (j.factorial : ℝ)) := by
    intro j
    have hfac : (k.factorial : ℝ) ≤ ((j + k).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (show k ≤ j + k by omega)
    have hleft : (a / 2) ^ (2 * j + k) /
        ((j.factorial : ℝ) * ((j + k).factorial : ℝ)) =
          (b ^ k * (b ^ 2) ^ j / (j.factorial : ℝ)) / ((j + k).factorial : ℝ) := by
      dsimp only [b]
      rw [pow_add, pow_mul]
      ring
    have hright : b ^ k / (k.factorial : ℝ) * ((b ^ 2) ^ j / (j.factorial : ℝ)) =
        (b ^ k * (b ^ 2) ^ j / (j.factorial : ℝ)) / (k.factorial : ℝ) := by ring
    rw [hleft, hright]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  have h := hs.summable.tsum_le_tsum hterm hm.summable
  rw [hs.tsum_eq, hm.tsum_eq] at h
  have hb2 : b ^ 2 = a ^ 2 / 4 := by dsimp [b]; ring
  simpa only [b, hb2] using h

/-- Absolute modified Bessel coefficients obey the same factorial bound for every real argument.
Source: Trefethen, ATAP, Exercise 3.15; absolute majorization of the factorial power series.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem abs_modifiedBesselCoeff_le_pow_div_factorial_mul_exp (a : ℝ) (k : ℕ) :
    |modifiedBesselCoeff a k| ≤ (|a| / 2) ^ k / (k.factorial : ℝ) * Real.exp (a ^ 2 / 4) := by
  have hs := hasSum_pow_div_factorial_modifiedBesselCoeff a k
  have hsabs := hasSum_pow_div_factorial_modifiedBesselCoeff |a| k
  have hterm : ∀ j : ℕ,
      ‖(a / 2) ^ (2 * j + k) / ((j.factorial : ℝ) * ((j + k).factorial : ℝ))‖ =
        (|a| / 2) ^ (2 * j + k) / ((j.factorial : ℝ) * ((j + k).factorial : ℝ)) := by
    intro j
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
      abs_of_nonneg (show (0 : ℝ) ≤ (j.factorial : ℝ) * ((j + k).factorial : ℝ) by positivity)]
  have hnorm : Summable (fun j : ℕ =>
      ‖(a / 2) ^ (2 * j + k) / ((j.factorial : ℝ) * ((j + k).factorial : ℝ))‖) := by
    simp_rw [hterm]
    exact hsabs.summable
  have h := norm_tsum_le_tsum_norm hnorm
  rw [hs.tsum_eq, Real.norm_eq_abs] at h
  simp_rw [hterm] at h
  rw [hsabs.tsum_eq] at h
  refine h.trans ?_
  have hb := modifiedBesselCoeff_le_pow_div_factorial_mul_exp (abs_nonneg a) k
  simpa only [sq_abs] using hb

/-- The entire sequence of modified Bessel coefficients is absolutely summable.
Source: Trefethen, ATAP, Exercise 3.15; the factorial bound and scalar exponential series.
Helper for `chebyshev-series-exp-bessel`. -/
theorem summable_abs_modifiedBesselCoeff (a : ℝ) :
    Summable (fun k => |modifiedBesselCoeff a k|) := by
  have hmajor : Summable (fun k : ℕ =>
      (|a| / 2) ^ k / (k.factorial : ℝ) * Real.exp (a ^ 2 / 4)) := by
    have h := (summable_abs_pow_div_factorial (|a| / 2)).mul_right (Real.exp (a ^ 2 / 4))
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ |a| / 2 by positivity)] using h
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_modifiedBesselCoeff_le_pow_div_factorial_mul_exp a) hmajor

/-- The genuine Chebyshev coefficients of an exponential are absolutely summable.
Source: Trefethen, ATAP, Exercise 3.15; helper for `chebyshev-series-exp-bessel`. -/
theorem summable_abs_chebyshevCoeff_exp (a : ℝ) :
    Summable (fun k => |chebyshevCoeff (fun x => Real.exp (a * x)) k|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((summable_abs_modifiedBesselCoeff a).mul_left 2)
  intro k
  rw [chebyshevCoeff_exp_eq_modifiedBesselCoeff, abs_mul]
  by_cases hk : k = 0
  · simp only [if_pos hk]
    norm_num
    nlinarith [abs_nonneg (modifiedBesselCoeff a k)]
  · simp [hk]

/-- The exponential has the genuine absolute Chebyshev expansion with modified Bessel coefficients.
Source: Trefethen, ATAP, Exercise 3.15. The integral coefficients, their factorial power series,
nonnegativity and sharp factorial bound are proved in this module.
atlas: chebyshev-series-exp-bessel -/
theorem hasSum_modifiedBesselCoeff_mul_eval_T (a : ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k => (if k = 0 then 1 else 2) * modifiedBesselCoeff a k * (T ℝ (k : ℤ)).eval x)
      (Real.exp (a * x)) := by
  have h := hasSum_chebyshevCoeff_mul_eval_T (f := fun x => Real.exp (a * x))
    (by fun_prop) (summable_abs_chebyshevCoeff_exp a) hx
  simpa only [chebyshevCoeff_exp_eq_modifiedBesselCoeff] using h

/-- Exponential Chebyshev truncations converge uniformly with their modified Bessel coefficients.
Source: Trefethen, ATAP, Exercise 3.15.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem tendstoUniformlyOn_chebyshevTrunc_exp (a : ℝ) :
    TendstoUniformlyOn (fun n x => (chebyshevTrunc (fun x => Real.exp (a * x)) n).eval x)
      (fun x => Real.exp (a * x)) Filter.atTop (Icc (-1 : ℝ) 1) :=
  tendstoUniformlyOn_chebyshevTrunc (by fun_prop) (summable_abs_chebyshevCoeff_exp a)

/-- The exponential truncation error is at most twice the omitted absolute Bessel coefficients.
Source: Trefethen, ATAP, Exercise 3.15.
atlas: chebyshev-series-exp-bessel (partial) -/
theorem abs_exp_sub_eval_chebyshevTrunc_le_modifiedBesselCoeff_tail (a : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |Real.exp (a * x) - (chebyshevTrunc (fun x => Real.exp (a * x)) n).eval x| ≤
      2 * ∑' j, |modifiedBesselCoeff a (j + (n + 1))| := by
  have h := abs_sub_eval_chebyshevTrunc_le_tsum (f := fun x => Real.exp (a * x))
    (by fun_prop) (summable_abs_chebyshevCoeff_exp a) n hx
  have hterm : ∀ j, |chebyshevCoeff (fun x => Real.exp (a * x)) (j + (n + 1))| =
      2 * |modifiedBesselCoeff a (j + (n + 1))| := by
    intro j
    rw [chebyshevCoeff_exp_eq_modifiedBesselCoeff, if_neg (by omega), abs_mul]
    norm_num
  simp_rw [hterm] at h
  simpa only [tsum_mul_left] using h

end NLAlib

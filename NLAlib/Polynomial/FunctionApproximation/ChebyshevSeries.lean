import NLAlib.Polynomial.FunctionApproximation.ChebyshevFourier
import NLAlib.Polynomial.FunctionApproximation.ChebyshevCoefficients
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Chebyshev reconstruction for absolutely summable coefficients

Continuous interval functions with summable coefficient norms have an absolute,
uniform Chebyshev expansion and a truncation error bounded by its coefficient tail.
The reconstruction uses Mathlib's continuous-circle Fourier inversion.
-/

noncomputable section

open Complex Set Metric Filter Polynomial Polynomial.Chebyshev Finset MeasureTheory
open scoped Topology ComplexConjugate Real

namespace NLAlib

open scoped NLAlib.TwoPi

/-- Absolute summability of genuine Chebyshev coefficients implies summability of the
full Fourier coefficient sequence of the cosine-circle pullback.
Source: Trefethen, ATAP, Theorem 3.1; helper for `chebyshev-series-convergence`. -/
theorem summable_fourierCoeff_realChebyshevCircleFunction {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) :
    Summable (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ))) := by
  have hbound : ∀ k : ℕ,
      ‖fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)‖ ≤
        |chebyshevCoeff f k| := by
    intro k
    let z := fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)
    have him : z.im = 0 := im_fourierCoeff_of_even_real _
      (even_realChebyshevCircleFunction f) _
    have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hc := chebyshevCoeff_eq_re_fourierCoeff hf k
    change chebyshevCoeff f k = (if k = 0 then 1 else 2) * z.re at hc
    change ‖z‖ ≤ |chebyshevCoeff f k|
    rw [hz, Complex.norm_real, Real.norm_eq_abs, hc]
    by_cases hk : k = 0
    · simp [hk]
    · simp only [if_neg hk, abs_mul]
      norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [abs_nonneg z.re]
  have hs_nat : Summable (fun k : ℕ =>
      fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hs).of_norm
  have hs_neg : Summable (fun k : ℕ =>
      fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (-((k : ℤ) + 1))) := by
    simp_rw [fourierCoeff_realChebyshevCircleFunction_neg]
    exact_mod_cast (summable_nat_add_iff 1).mpr hs_nat
  exact Summable.of_nat_of_neg_add_one hs_nat hs_neg

/-- Opposite Fourier frequencies combine to one positive Chebyshev term.
Source: Trefethen, ATAP, Theorem 3.1; helper for `chebyshev-series-convergence`. -/
theorem re_fourier_pair_eq_chebyshevCoeff_mul_eval_T {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    ((fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ) *
      fourier (k : ℤ) (θ : AddCircle (2 * Real.pi))) +
      (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (-(k : ℤ)) *
        fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)))).re =
      chebyshevCoeff f k * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
  rw [fourierCoeff_realChebyshevCircleFunction_neg, ← mul_add, fourier_neg,
    Complex.add_conj, T_real_cos, re_fourier_nat_coe_eq_cos,
    chebyshevCoeff_eq_re_fourierCoeff hf, if_neg hk.ne']
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Int.cast_natCast]
  ring

/-- Absolutely summable genuine Chebyshev coefficients reconstruct a continuous function
at every cosine argument.
Source: Trefethen, ATAP, Theorem 3.1(a); Mathlib continuous Fourier reconstruction.
Helper for `chebyshev-series-convergence`. -/
theorem hasSum_chebyshevCoeff_mul_eval_T_cos {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) (θ : ℝ) :
    HasSum (fun k : ℕ => chebyshevCoeff f k * (T ℝ (k : ℤ)).eval (Real.cos θ))
      (f (Real.cos θ)) := by
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨(fun t => (realChebyshevCircleFunction f t : ℂ)),
      Complex.continuous_ofReal.comp (continuous_realChebyshevCircleFunction hf)⟩
  let u : ℤ → ℂ := fun k => fourierCoeff g k * fourier k (θ : AddCircle (2 * Real.pi))
  have hu : HasSum u (f (Real.cos θ) : ℂ) := by
    simpa only [u, g, ContinuousMap.coe_mk, smul_eq_mul,
      realChebyshevCircleFunction_coe] using
      has_pointwise_sum_fourier_series_of_summable (f := g)
        (summable_fourierCoeff_realChebyshevCircleFunction hf hs) (θ : AddCircle (2 * Real.pi))
  have hp : Summable (fun k : ℕ => u (k : ℤ)) :=
    hu.summable.comp_injective Nat.cast_injective
  have hn : Summable (fun k : ℕ => u (-((k + 1 : ℕ) : ℤ))) :=
    hu.summable.comp_injective (show Function.Injective (fun k : ℕ => -((k + 1 : ℕ) : ℤ)) by
      intro a b hab
      have h := neg_injective hab
      exact Nat.add_right_cancel (Int.natCast_inj.mp h))
  have hps : Summable (fun k : ℕ => u ((k + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).mpr hp
  have hsum : (∑' k : ℕ, u (k : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ))) =
      (f (Real.cos θ) : ℂ) := by
    rw [← hu.tsum_eq]
    exact (tsum_of_nat_of_neg_add_one hp hn).symm
  have hsplit := hp.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at hsplit
  have hpair := Complex.reCLM.hasSum (hps.hasSum.add hn.hasSum)
  have hterm : ∀ k : ℕ,
      (u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ))).re =
        chebyshevCoeff f (k + 1) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) := by
    intro k
    exact re_fourier_pair_eq_chebyshevCoeff_mul_eval_T hf (Nat.succ_pos k) θ
  change HasSum (fun k : ℕ => (u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ))).re)
    ((∑' k : ℕ, u ((k + 1 : ℕ) : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ)))).re at hpair
  simp_rw [hterm] at hpair
  have hfull := hpair.zero_add (f := fun k : ℕ =>
    chebyshevCoeff f k * (T ℝ (k : ℤ)).eval (Real.cos θ))
  have hzero : chebyshevCoeff f 0 * (T ℝ (0 : ℤ)).eval (Real.cos θ) = (u 0).re := by
    simp [chebyshevCoeff_eq_re_fourierCoeff hf, u, g]
  simp only [Nat.cast_zero] at hfull hsplit
  rw [hzero] at hfull
  have heq : (u 0).re +
      ((∑' k : ℕ, u ((k + 1 : ℕ) : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ)))).re =
        f (Real.cos θ) := by
    rw [← Complex.add_re, ← add_assoc, hsplit, hsum, Complex.ofReal_re]
  rw [heq] at hfull
  exact hfull

/-- Continuous functions with absolutely summable genuine Chebyshev coefficients have
an absolute Chebyshev expansion at every point of the unit interval.
Source: Trefethen, ATAP, Theorem 3.1(a).
atlas: chebyshev-series-convergence (partial) -/
theorem hasSum_chebyshevCoeff_mul_eval_T {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x) (f x) := by
  simpa only [Real.cos_arccos hx.1 hx.2] using
    hasSum_chebyshevCoeff_mul_eval_T_cos hf hs (Real.arccos x)

/-- The Chebyshev truncation error is bounded by the absolute coefficient tail.
Source: Trefethen, ATAP, Theorem 3.1(a).
atlas: chebyshev-series-convergence (partial) -/
theorem abs_sub_eval_chebyshevTrunc_le_tsum {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |f x - (chebyshevTrunc f n).eval x| ≤ ∑' j, |chebyshevCoeff f (j + (n + 1))| := by
  let u : ℕ → ℝ := fun k => chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x
  have hu : HasSum u (f x) := hasSum_chebyshevCoeff_mul_eval_T hf hs hx
  have hsplit := hu.summable.sum_add_tsum_nat_add (n + 1)
  rw [hu.tsum_eq] at hsplit
  have hp : (chebyshevTrunc f n).eval x = ∑ k ∈ range (n + 1), u k := by
    simp only [chebyshevTrunc, eval_finsetSum, eval_mul, eval_C, u]
  have herr : f x - (chebyshevTrunc f n).eval x = ∑' j, u (j + (n + 1)) := by
    rw [hp]
    linarith
  have hterm : ∀ j, ‖u (j + (n + 1))‖ ≤ |chebyshevCoeff f (j + (n + 1))| := by
    intro j
    dsimp [u]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_eval_T_real_le_one _ (abs_le.mpr hx))
      (abs_nonneg _)).trans_eq (mul_one _)
  have hstail := (summable_nat_add_iff (n + 1)).mpr hs
  have hnorm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hstail
  rw [herr, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm hstail)

/-- Absolutely summable Chebyshev series converge uniformly on the full closed interval.
Source: Trefethen, ATAP, Theorem 3.1(a).
atlas: chebyshev-series-convergence (partial) -/
theorem tendstoUniformlyOn_chebyshevTrunc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) :
    TendstoUniformlyOn (fun n x => (chebyshevTrunc f n).eval x) f atTop (Icc (-1 : ℝ) 1) := by
  have hbound : ∀ k x, x ∈ Icc (-1 : ℝ) 1 →
      ‖chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x‖ ≤ |chebyshevCoeff f k| := by
    intro k x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_eval_T_real_le_one _ (abs_le.mpr hx))
      (abs_nonneg _)).trans_eq (mul_one _)
  have hu := tendstoUniformlyOn_tsum_nat hs hbound
  have hshift : TendstoUniformlyOn
      (fun n x => ∑ k ∈ range (n + 1), chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x)
      (fun x => ∑' k, chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x) atTop
      (Icc (-1 : ℝ) 1) := fun v hv => (tendsto_add_atTop_nat 1).eventually (hu v hv)
  have heq : EqOn (fun x => ∑' k, chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x) f
      (Icc (-1 : ℝ) 1) := fun x hx => (hasSum_chebyshevCoeff_mul_eval_T hf hs hx).tsum_eq
  convert hshift.congr_right heq using 1
  simp only [chebyshevTrunc, eval_finsetSum, eval_mul, eval_C]

end NLAlib

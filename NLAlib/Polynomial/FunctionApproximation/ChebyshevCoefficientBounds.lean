import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite Chebyshev coefficient estimates

Parseval and finite Cauchy--Schwarz give a square-root-cardinality bound on any
finite group of coefficients. This supports absolute convergence from Jackson
approximation on dyadic frequency blocks.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set MeasureTheory
open scoped Topology Real ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- A finite set of Fourier coefficients of a bounded continuous cosine pullback has
square sum at most the squared function bound.
Source: Mathlib Parseval identity; helper for `chebyshev-series-convergence`. -/
theorem sum_norm_sq_fourierCoeff_realChebyshevCircleFunction_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) (s : Finset ℕ) :
    (∑ k ∈ s, ‖fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)‖ ^ 2) ≤ M ^ 2 := by
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨(fun t => (realChebyshevCircleFunction f t : ℂ)),
      Complex.continuous_ofReal.comp (continuous_realChebyshevCircleFunction hf)⟩
  let gLp := g.toLp 2 AddCircle.haarAddCircle ℂ
  have hP := hasSum_sq_fourierCoeff gLp
  simp only [gLp, fourierCoeff_toLp] at hP
  have hfinite := hP.summable.sum_le_tsum (s.map ⟨(fun k : ℕ => (k : ℤ)), Nat.cast_injective⟩)
    (fun i hi => sq_nonneg _)
  rw [hP.tsum_eq] at hfinite
  simp only [sum_map, Function.Embedding.coeFn_mk] at hfinite
  refine hfinite.trans ?_
  have hAe : ∀ᵐ t ∂AddCircle.haarAddCircle, gLp t = g t :=
    g.coeFn_toLp AddCircle.haarAddCircle
  rw [integral_congr_ae (hAe.mono (fun t ht => by rw [ht]))]
  have hgi : Integrable (fun t => ‖g t‖ ^ 2) AddCircle.haarAddCircle :=
    (g.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : ∀ t, ‖g t‖ ^ 2 ≤ M ^ 2 := by
    intro t
    apply pow_le_pow_left₀ (norm_nonneg _) _
    change ‖(realChebyshevCircleFunction f t : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM _ (re_fourier_one_mem_Icc t)
  exact (integral_mono hgi (integrable_const (M ^ 2)) hb).trans_eq (by simp)

/-- The sum of absolute values of any finite set of Chebyshev coefficients is at most
`2√card * M` when the function is bounded by `M` on the interval.
Source: finite Cauchy--Schwarz and Parseval; helper for `chebyshev-series-convergence`. -/
theorem sum_abs_chebyshevCoeff_le_sqrt_card_mul {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) (s : Finset ℕ) :
    (∑ k ∈ s, |chebyshevCoeff f k|) ≤ 2 * √(s.card : ℝ) * M := by
  have hcoeff : ∀ k, |chebyshevCoeff f k| ≤
      2 * ‖fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)‖ := by
    intro k
    rw [chebyshevCoeff_eq_re_fourierCoeff hf, abs_mul]
    have hz := Complex.abs_re_le_norm
      (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ))
    split_ifs <;> norm_num <;> nlinarith [norm_nonneg
      (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ))]
  have hsquares : (∑ k ∈ s, |chebyshevCoeff f k| ^ 2) ≤ 4 * M ^ 2 := by
    calc (∑ k ∈ s, |chebyshevCoeff f k| ^ 2) ≤
        ∑ k ∈ s, 4 * ‖fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)‖ ^ 2 := by
          apply sum_le_sum
          intro k hk
          nlinarith [hcoeff k, abs_nonneg (chebyshevCoeff f k), norm_nonneg
            (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ))]
      _ = 4 * ∑ k ∈ s, ‖fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)‖ ^ 2 := by
          rw [mul_sum]
      _ ≤ 4 * M ^ 2 := mul_le_mul_of_nonneg_left
        (sum_norm_sq_fourierCoeff_realChebyshevCircleFunction_le hf hM0 hM s) (by norm_num)
  have hcauchy := sum_mul_sq_le_sq_mul_sq s (fun k => |chebyshevCoeff f k|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcauchy
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ s.card by positivity)
  have hnonneg : 0 ≤ ∑ k ∈ s, |chebyshevCoeff f k| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hsquares (show (0 : ℝ) ≤ s.card by positivity)
  have hsquare : (∑ k ∈ s, |chebyshevCoeff f k|) ^ 2 ≤ (2 * √(s.card : ℝ) * M) ^ 2 := by
    calc _ ≤ (∑ k ∈ s, |chebyshevCoeff f k| ^ 2) * s.card := hcauchy
      _ ≤ 4 * M ^ 2 * s.card := hmul
      _ = (2 * √(s.card : ℝ) * M) ^ 2 := by simp only [mul_pow, hc]; ring
  exact (sq_le_sq₀ hnonneg (by positivity)).mp hsquare

end NLAlib

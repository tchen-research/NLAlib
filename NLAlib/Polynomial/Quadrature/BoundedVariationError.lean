import NLAlib.Polynomial.Quadrature.GaussError
import NLAlib.Polynomial.FunctionApproximation.ChebyshevDifferentiable

/-! # Corrected bounded-variation quadrature constants

The actual Clenshaw–Curtis rule and symmetric positive Gauss rules use the
sharp even descending-factorial tail, including the corrected Gauss denominator.
-/
noncomputable section
open Set MeasureTheory Polynomial Polynomial.Chebyshev
namespace NLAlib

/-- Under the full AC/BV derivative-chain hypotheses, the actual Clenshaw–Curtis
rule has error `32V/(15πν(n−ν)^ν)`. Source: Trefethen, ATAP, Theorem 19.3;
finite aliasing and the exact descending-factorial coefficient envelope.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_clenshawCurtisRule_le_of_bv {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν < n) (hn2 : 2 ≤ n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    |(∫ x in (-1 : ℝ)..1, F 0 x) - clenshawCurtisRule n (F 0)| ≤
      32 * V / (15 * Real.pi * ν * ((n : ℝ) - ν) ^ ν) := by
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hcS := summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV
  have hf : ContinuousOn (F 0) (Icc (-1 : ℝ) 1) := by simpa using (hAC 0 hν).continuousOn
  have htail := tsum_even_abs_tail_le_of_descFactorial hcS hν hn
    (show 0 ≤ 2 * V / Real.pi by positivity) (fun k hk => by
      have h := abs_chebyshevCoeff_le_descFactorial hAC hderiv hBV hV hk
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h)
  have h := abs_integral_sub_clenshawCurtisRule_le_even_tail hcS
    (fun x hx => hasSum_chebyshevCoeff_mul_eval_T hf hcS hx) hn2
  refine h.trans ?_
  have hmul := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 32 / 15)
  convert hmul using 1
  ring

/-- A symmetric positive rule exact through degree `2n+1` has the corrected Gauss
BV error `32V/(15πν(2n+1−ν)^ν)`. Source: Trefethen, ATAP, Theorem 19.4 and official
2013-edition errata to (19.10). The supplied node-and-weight permutation states reflection explicitly.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_symmetric_quadrature_le_of_bv
    {ι : Type*} [Fintype ι] (v w : ι → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 2)
    (σ : ι ≃ ι) (hvσ : ∀ i, v (σ i) = -v i) (hwσ : ∀ i, w (σ i) = w i)
    {n ν : ℕ} (hn : 1 ≤ n) (hν : 0 < ν) (hnν : ν < 2 * n + 1)
    (hexact : ∀ p : ℝ[X], p.degree ≤ (2 * n + 1 : ℕ) →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ i, w i * p.eval (v i))
    {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    |(∫ x in (-1 : ℝ)..1, F 0 x) - ∑ i, w i * F 0 (v i)| ≤
      32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν) := by
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hcS := summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV
  have hf : ContinuousOn (F 0) (Icc (-1 : ℝ) 1) := by simpa using (hAC 0 hν).continuousOn
  have htail := tsum_even_abs_tail_le_of_descFactorial hcS hν hnν
    (show 0 ≤ 2 * V / Real.pi by positivity) (fun k hk => by
      have h := abs_chebyshevCoeff_le_descFactorial hAC hderiv hBV hV hk
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h)
  have h := abs_integral_sub_symmetric_quadrature_le_even_tail v w hv hw hmass σ hvσ hwσ hn hexact hcS
    (fun x hx => hasSum_chebyshevCoeff_mul_eval_T hf hcS hx)
  refine h.trans ?_
  have hmul := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 32 / 15)
  push_cast at hmul
  convert hmul using 1
  ring

end NLAlib

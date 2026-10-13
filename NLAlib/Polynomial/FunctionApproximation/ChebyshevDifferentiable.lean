import NLAlib.Polynomial.FunctionApproximation.ChebyshevBoundedVariation
import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import NLAlib.Polynomial.Interpolation.ChebyshevSeriesInterpolation
import NLAlib.Polynomial.BestApproximation.MinimaxError
import NLAlib.ForMathlib.Analysis.DescendingFactorialSeries

/-!
# Differentiable Chebyshev approximation

The exact BV coefficient envelope has a telescoping tail. It gives the
truncation, interpolation, and minimax bounds of ATAP Theorem 7.2.
Atlas: `chebyshev-approx-differentiable`.
-/

noncomputable section

open Real Set MeasureTheory Filter Polynomial

namespace NLAlib

/-- A positive-order AC/BV derivative chain gives absolutely summable Chebyshev coefficients.
Source: ATAP Thms 7.1 and 3.1; helper for `chebyshev-approx-differentiable`. -/
theorem summable_abs_chebyshevCoeff_of_bv {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    Summable (fun k => |chebyshevCoeff (F 0) k|) := by
  have hs := (summable_inv_cast_descFactorial_tail hν (le_refl ν)).mul_left (2 * V / Real.pi)
  apply (summable_nat_add_iff (ν + 1)).mp
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hs
  intro j
  have hb := abs_chebyshevCoeff_le_descFactorial hAC hderiv hBV hV
    (k := j + (ν + 1)) (by omega)
  simpa only [Nat.add_comm, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hb

/-- The absolute coefficient tail is bounded by the exact shorter descending factorial.
Source: focused BV reroutes, telescoping tail; helper for `chebyshev-approx-differentiable`. -/
theorem tsum_abs_chebyshevCoeff_tail_le_descFactorial {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν ≤ n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    (∑' j, |chebyshevCoeff (F 0) (j + (n + 1))|) ≤
      2 * V / (Real.pi * ν * (n.descFactorial ν : ℝ)) := by
  have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hs := (summable_inv_cast_descFactorial_tail hν hn).mul_left (2 * V / Real.pi)
  have hcoeff := (summable_nat_add_iff (n + 1)).mpr
    (summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV)
  calc
    _ ≤ ∑' j, (2 * V / Real.pi) * ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹ := by
      apply hcoeff.tsum_le_tsum _ hs
      intro j
      have hb := abs_chebyshevCoeff_le_descFactorial hAC hderiv hBV hV
        (k := j + (n + 1)) (by omega)
      simpa only [Nat.add_comm, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hb
    _ = (2 * V / Real.pi) * ∑' j, ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹ :=
      tsum_mul_left
    _ ≤ (2 * V / Real.pi) * ((n.descFactorial ν : ℝ)⁻¹ / ν) :=
      mul_le_mul_of_nonneg_left (tsum_inv_cast_descFactorial_tail_le hν hn) (by positivity)
    _ = _ := by ring

/-- The usual algebraic tail bound follows from the stronger descending-factorial bound.
Source: Trefethen, ATAP, proof of Thm 7.2; helper for `chebyshev-approx-differentiable`. -/
theorem tsum_abs_chebyshevCoeff_tail_le_pow {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν < n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    (∑' j, |chebyshevCoeff (F 0) (j + (n + 1))|) ≤
      2 * V / (Real.pi * ν * ((n : ℝ) - ν) ^ ν) := by
  have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hpow : ((n : ℝ) - ν) ^ ν ≤ (n.descFactorial ν : ℝ) := by
    rw [← Nat.cast_sub hn.le, ← Nat.cast_pow]
    exact_mod_cast (show (n - ν) ^ ν ≤ n.descFactorial ν from
      (Nat.pow_le_pow_left (by omega : n - ν ≤ n + 1 - ν) ν).trans
        (Nat.pow_sub_le_descFactorial n ν))
  have hnreal : (ν : ℝ) < n := by exact_mod_cast hn
  have hνreal : (0 : ℝ) < ν := by exact_mod_cast hν
  exact (tsum_abs_chebyshevCoeff_tail_le_descFactorial hν hn.le hAC hderiv hBV hV).trans
    (div_le_div_of_nonneg_left (by positivity)
      (mul_pos (mul_pos pi_pos hνreal) (pow_pos (sub_pos.mpr hnreal) ν))
      (mul_le_mul_of_nonneg_left hpow (by positivity)))

/-- Chebyshev truncation has the sharp `2V/(πν(n−ν)^ν)` differentiable error bound.
Source: Trefethen, ATAP, Thm 7.2; explicit AC/BV derivative representatives.
atlas: chebyshev-approx-differentiable -/
theorem abs_sub_eval_chebyshevTrunc_le_of_bv {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν < n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |F 0 x - (chebyshevTrunc (F 0) n).eval x| ≤
      2 * V / (Real.pi * ν * ((n : ℝ) - ν) ^ ν) := by
  have hf : ContinuousOn (F 0) (Icc (-1 : ℝ) 1) := by
    simpa using (hAC 0 hν).continuousOn
  exact (abs_sub_eval_chebyshevTrunc_le_tsum hf
    (summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV) n hx).trans
    (tsum_abs_chebyshevCoeff_tail_le_pow hν hn hAC hderiv hBV hV)

/-- Chebyshev interpolation has the sharp `4V/(πν(n−ν)^ν)` differentiable error bound.
Source: Trefethen, ATAP, Thm 7.2, on the Chebyshev extrema grid.
atlas: chebyshev-approx-differentiable -/
theorem abs_sub_eval_chebyshevInterpolant_le_of_bv {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν < n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |F 0 x - (chebyshevInterpolant (F 0) n).eval x| ≤
      4 * V / (Real.pi * ν * ((n : ℝ) - ν) ^ ν) := by
  have hf : ContinuousOn (F 0) (Icc (-1 : ℝ) 1) := by
    simpa using (hAC 0 hν).continuousOn
  have hb := abs_sub_eval_chebyshevInterpolant_le_two_mul_tsum hf
    (summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV) (by omega : 0 < n) hx
  exact hb.trans ((mul_le_mul_of_nonneg_left
    (tsum_abs_chebyshevCoeff_tail_le_pow hν hn hAC hderiv hBV hV)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- The differentiable bound is attained by an explicit degree-bounded polynomial.
Source: Trefethen, ATAP, Thm 7.2; the existential approximation interface.
atlas: chebyshev-approx-differentiable -/
theorem exists_degree_le_approx_of_bv {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : ν < n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |F 0 x - p.eval x| ≤ 2 * V / (Real.pi * ν * ((n : ℝ) - ν) ^ ν) :=
  ⟨chebyshevTrunc (F 0) n, degree_chebyshevTrunc_le (F 0) n,
    fun _ hx => abs_sub_eval_chebyshevTrunc_le_of_bv hν hn hAC hderiv hBV hV hx⟩

/-- The canonical minimax error obeys the same differentiable approximation bound.
Source: Trefethen, ATAP, Thm 7.2; the truncation is a degree-bounded competitor.
atlas: chebyshev-approx-differentiable -/
theorem minimaxError_le_of_bv (f : C(Icc (-1 : ℝ) 1, ℝ))
    {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hF : ∀ x : Icc (-1 : ℝ) 1, F 0 x = f x)
    (hν : 0 < ν) (hn : ν < n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    minimaxError n f ≤ 2 * V / (Real.pi * ν * ((n : ℝ) - ν) ^ ν) := by
  have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hdiff : 0 ≤ (n : ℝ) - ν := sub_nonneg.mpr (by exact_mod_cast hn.le)
  have hmem : (chebyshevTrunc (F 0) n).toContinuousMapOn (Icc (-1 : ℝ) 1) ∈
      polynomialApproximationSpace (Icc (-1 : ℝ) 1) n :=
    mem_polynomialApproximationSpace_iff.mpr
      ⟨chebyshevTrunc (F 0) n, degree_chebyshevTrunc_le (F 0) n, rfl⟩
  apply (minimaxError_le_norm_sub f hmem).trans
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change |f x - (chebyshevTrunc (F 0) n).eval (x : ℝ)| ≤ _
  rw [← hF x]
  exact abs_sub_eval_chebyshevTrunc_le_of_bv hν hn hAC hderiv hBV hV x.property

end NLAlib

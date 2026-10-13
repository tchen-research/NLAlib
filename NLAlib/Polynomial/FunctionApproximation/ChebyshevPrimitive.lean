import NLAlib.Polynomial.FunctionApproximation.ChebyshevCoefficients
import NLAlib.ForMathlib.MeasureTheory.AbsoluteContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Endpoint-integrable primitives of the Chebyshev weight

The sine of a multiple of `arccos` is absolutely continuous on the entire closed
interval. Its derivative has the integrable Chebyshev endpoint singularity.
Helpers for `chebyshev-coeff-bv-decay`, following the focused reroutes.
-/

noncomputable section

open Real Set Polynomial Polynomial.Chebyshev MeasureTheory Filter

namespace NLAlib

/-- On the interval interior, the sine primitive has the weighted Chebyshev derivative.
Source: focused reroutes, Lemma `lem:FkAC`; helper for `chebyshev-coeff-bv-decay`. -/
theorem hasDerivAt_sin_mul_arccos (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => sin ((k : ℝ) * arccos t))
      (-(k : ℝ) * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) x := by
  have h := (hasDerivAt_sin ((k : ℝ) * arccos x)).comp x
    ((hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).const_mul (k : ℝ))
  have hT : (T ℝ (k : ℤ)).eval x = cos ((k : ℝ) * arccos x) := by
    calc
      (T ℝ (k : ℤ)).eval x = (T ℝ (k : ℤ)).eval (cos (arccos x)) :=
        congrArg (fun t : ℝ => (T ℝ (k : ℤ)).eval t) (cos_arccos hx.1.le hx.2.le).symm
      _ = cos ((k : ℝ) * arccos x) := by simp only [T_real_cos, Int.cast_natCast]
  have hval : cos ((k : ℝ) * arccos x) * ((k : ℝ) * -(1 / √(1 - x ^ 2))) =
      -(k : ℝ) * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹ := by
    rw [hT]
    simp only [one_div, Real.sqrt_inv]
    ring
  rw [hval] at h
  simpa only [Function.comp_def] using h

/-- The derivative of the sine primitive is integrable despite its endpoint singularity.
Source: focused reroutes, Lemma `lem:FkAC`; helper for `chebyshev-coeff-bv-decay`. -/
theorem intervalIntegrable_sin_mul_arccos_deriv (k : ℕ) :
    IntervalIntegrable (fun x => -(k : ℝ) * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹)
      volume (-1) 1 := by
  have h : IntervalIntegrable (fun x => (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹)
      volume (-1) 1 := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul (by fun_prop)
  simpa only [mul_assoc] using h.const_mul (-(k : ℝ))

/-- Integrating the weighted derivative recovers the sine primitive, including endpoints.
Source: focused reroutes, Lemma `lem:FkAC`; helper for `chebyshev-coeff-bv-decay`. -/
theorem integral_sin_mul_arccos_deriv (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∫ t in -1..x, -(k : ℝ) * (T ℝ (k : ℤ)).eval t * √(1 - t ^ 2)⁻¹) =
      sin ((k : ℝ) * arccos x) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (f := fun t => sin ((k : ℝ) * arccos t)) (by fun_prop)
    (fun t ht => hasDerivAt_sin_mul_arccos k ⟨ht.1, ht.2.trans_le hx.2⟩)
    ((intervalIntegrable_sin_mul_arccos_deriv k).mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hx.2))
  simpa only [arccos_neg_one, sin_nat_mul_pi, sub_zero] using h

/-- The weighted sine primitive is absolutely continuous on `[-1,1]`.
Source: focused reroutes, Lemma `lem:FkAC`; helper for `chebyshev-coeff-bv-decay`. -/
theorem absolutelyContinuousOnInterval_sin_mul_arccos (k : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => sin ((k : ℝ) * arccos x)) (-1) 1 := by
  have h := (intervalIntegrable_sin_mul_arccos_deriv k).absolutelyContinuousOnInterval_intervalIntegral
    (c := -1) (by simp)
  apply absolutelyContinuousOnInterval_congr (f := fun x =>
    ∫ t in -1..x, -(k : ℝ) * (T ℝ (k : ℤ)).eval t * √(1 - t ^ 2)⁻¹) _ h
  intro x hx
  exact integral_sin_mul_arccos_deriv k (by simpa using hx)

end NLAlib

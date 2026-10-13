import NLAlib.Polynomial.FunctionApproximation.ChebyshevPrimitive
import NLAlib.ForMathlib.Analysis.FourierBoundedVariation

/-!
# Integration by parts for Chebyshev coefficients

The endpoint-integrable sine primitive gives the ordinary AC integral identity
behind coefficient decay. Helpers for `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Real Set Polynomial Polynomial.Chebyshev MeasureTheory Filter

namespace NLAlib

/-- AC integration by parts expresses a positive Chebyshev coefficient using its derivative.
Source: focused reroutes, Lemma `lem:ip`; helper for `chebyshev-coeff-bv-decay`.
The derivative representative is specified almost everywhere on the interval. -/
theorem chebyshevCoeff_eq_integral_derivative {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u (-1) 1)
    (huv : ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv u x = v x)
    {k : ℕ} (hk : 0 < k) :
    chebyshevCoeff u k = 2 / (Real.pi * k) *
      ∫ x in -1..1, v x * sin ((k : ℝ) * arccos x) := by
  have hleft : (∫ x in -1..1, u x * deriv (fun t => sin ((k : ℝ) * arccos t)) x) =
      -(k : ℝ) * (∫ x in -1..1, u x * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) := by
    calc
      _ = ∫ x in -1..1, u x * (-(k : ℝ) * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp only
        rw [(hasDerivAt_sin_mul_arccos k hx).deriv]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
  have hright : (∫ x in -1..1, deriv u x * sin ((k : ℝ) * arccos x)) =
      ∫ x in -1..1, v x * sin ((k : ℝ) * arccos x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [huv] with x hx hxi
    rw [hx (by simpa using uIoc_subset_uIcc hxi)]
  have hibp := hu.integral_mul_deriv_eq_deriv_mul (absolutelyContinuousOnInterval_sin_mul_arccos k)
  rw [hleft, hright] at hibp
  simp only [arccos_one, mul_zero, sin_zero, arccos_neg_one, sin_nat_mul_pi,
    sub_zero, zero_sub] at hibp
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hj : (∫ x in -1..1, u x * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) =
      (∫ x in -1..1, v x * sin ((k : ℝ) * arccos x)) / k := by
    apply (eq_div_iff hkreal).mpr
    linarith [hibp]
  rw [chebyshevCoeff_eq_weighted_integral, if_neg hk.ne', hj]
  ring

/-- Cosine substitution turns the derivative integral into a finite trigonometric identity.
Source: focused reroutes, Lemma `lem:ip`; helper for `chebyshev-coeff-bv-decay`. -/
theorem integral_mul_sin_arccos_eq (v : ℝ → ℝ) (k : ℕ) :
    (∫ x in -1..1, v x * sin ((k : ℝ) * arccos x)) =
      ∫ θ in 0..Real.pi, v (cos θ) * (sin ((k : ℝ) * θ) * sin θ) := by
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun x => v x * sin ((k : ℝ) * arccos x))
    (f := cos) (f' := fun θ => -sin θ) (a := 0) (b := Real.pi)
    (by fun_prop) (fun θ _ => hasDerivAt_cos θ)
    (fun θ hθ => neg_nonpos.mpr (sin_nonneg_of_nonneg_of_le_pi
      (by simpa only [min_eq_left pi_pos.le] using hθ.1.le)
      (by simpa only [max_eq_right pi_pos.le] using hθ.2.le)))
  have hi : (∫ θ in 0..Real.pi,
      ((fun x => v x * sin ((k : ℝ) * arccos x)) ∘ cos) θ * -sin θ) =
      -(∫ θ in 0..Real.pi, v (cos θ) * (sin ((k : ℝ) * θ) * sin θ)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    have ht : θ ∈ Icc (0 : ℝ) Real.pi := by simpa only [uIcc_of_le pi_pos.le] using hθ
    simp only [Function.comp_apply, arccos_cos ht.1 ht.2]
    ring
  rw [hi, cos_zero, cos_pi, intervalIntegral.integral_symm (a := -1) (b := 1)] at hs
  exact neg_injective hs.symm

/-- Cosine coefficients of a BV representative have ordinary integrable cosine integrands.
Source: monotone substitution and Jordan decomposition; helper for `chebyshev-coeff-bv-decay`. -/
theorem intervalIntegrable_bv_cosine {v : ℝ → ℝ}
    (hv : BoundedVariationOn v (Icc (-1 : ℝ) 1)) (j : ℕ) :
    IntervalIntegrable (fun θ => v (cos θ) * cos ((j : ℝ) * θ)) volume 0 Real.pi := by
  have h : BoundedVariationOn (v ∘ cos) (uIcc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le pi_pos.le] using boundedVariationOn_comp_cos hv
  exact (intervalIntegrable_of_boundedVariationOn h).mul_continuousOn (by fun_prop)

/-- A derivative representative shifts a positive Chebyshev coefficient by one in each direction.
Source: focused reroutes, equation `eq:rec`; helper for `chebyshev-coeff-bv-decay`.
The `k=1` normalization is handled in `chebyshevCoeff_one_eq_derivative`. -/
theorem chebyshevCoeff_eq_sub_derivative {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u (-1) 1)
    (huv : ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv u x = v x)
    (hv : BoundedVariationOn v (Icc (-1 : ℝ) 1))
    {k : ℕ} (hk : 2 ≤ k) :
    chebyshevCoeff u k = (chebyshevCoeff v (k - 1) - chebyshevCoeff v (k + 1)) / (2 * k) := by
  have hsin : ∀ θ : ℝ, v (cos θ) * (sin ((k : ℝ) * θ) * sin θ) =
      (v (cos θ) * cos (((k - 1 : ℕ) : ℝ) * θ) -
        v (cos θ) * cos (((k + 1 : ℕ) : ℝ) * θ)) / 2 := by
    intro θ
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, Nat.cast_add, Nat.cast_one]
    rw [sub_mul, add_mul, one_mul, cos_sub, cos_add]
    ring
  rw [chebyshevCoeff_eq_integral_derivative hu huv (by omega : 0 < k),
    integral_mul_sin_arccos_eq]
  simp_rw [hsin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (intervalIntegrable_bv_cosine hv (k - 1)) (intervalIntegrable_bv_cosine hv (k + 1))]
  simp only [chebyshevCoeff_eq_cosine_integral, if_neg (show k - 1 ≠ 0 by omega),
    if_neg (show k + 1 ≠ 0 by omega)]
  ring

/-- The first Chebyshev coefficient has the special undoubled zeroth derivative coefficient.
Source: focused reroutes, equation `eq:rec1`; helper for `chebyshev-coeff-bv-decay`. -/
theorem chebyshevCoeff_one_eq_derivative {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u (-1) 1)
    (huv : ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv u x = v x)
    (hv : BoundedVariationOn v (Icc (-1 : ℝ) 1)) :
    chebyshevCoeff u 1 = chebyshevCoeff v 0 - chebyshevCoeff v 2 / 2 := by
  have hsin : ∀ θ : ℝ, v (cos θ) * (sin ((1 : ℕ) * θ) * sin θ) =
      (v (cos θ) * cos (((0 : ℕ) : ℝ) * θ) -
        v (cos θ) * cos (((2 : ℕ) : ℝ) * θ)) / 2 := by
    intro θ
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, one_mul, zero_mul, cos_zero]
    rw [cos_two_mul]
    rw [show sin θ * sin θ = 1 - cos θ ^ 2 by nlinarith [sin_sq_add_cos_sq θ]]
    ring
  rw [chebyshevCoeff_eq_integral_derivative hu huv (by omega : 0 < (1 : ℕ)),
    integral_mul_sin_arccos_eq]
  simp_rw [hsin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (intervalIntegrable_bv_cosine hv 0) (intervalIntegrable_bv_cosine hv 2)]
  simp only [chebyshevCoeff_eq_cosine_integral, Nat.cast_zero, Nat.cast_one, ite_true,
    if_neg (by norm_num : (2 : ℕ) ≠ 0), zero_mul, cos_zero]
  ring

end NLAlib

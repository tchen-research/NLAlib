import NLAlib.Polynomial.FunctionApproximation.ChebyshevIntegrationByParts
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Chebyshev coefficient decay from bounded variation

The AC derivative chain and a BV last derivative give the exact descending
factorial denominator, including the zero-derivative-order case.
Atlas: `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace NLAlib

/-- A BV function has the sharp positive-index Chebyshev coefficient bound.
Source: focused reroutes, Lemma `lem:bvbase`; helper for `chebyshev-coeff-bv-decay`. -/
theorem abs_chebyshevCoeff_le_variation_div {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    |chebyshevCoeff f k| ≤ 2 * (eVariationOn f (Icc (-1 : ℝ) 1)).toReal / (Real.pi * k) := by
  have hcomp := boundedVariationOn_comp_cos hf
  have hv : (eVariationOn (f ∘ cos) (Icc (0 : ℝ) Real.pi)).toReal ≤
      (eVariationOn f (Icc (-1 : ℝ) 1)).toReal :=
    ENNReal.toReal_mono hf (variationOn_comp_cos_le f)
  have hbound := abs_integral_mul_cos_le_variation_div hcomp hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [chebyshevCoeff_eq_cosine_integral, if_neg hk.ne', abs_mul,
    abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) pi_pos)]
  calc
    _ ≤ (2 / Real.pi) * ((eVariationOn (f ∘ cos) (Icc (0 : ℝ) Real.pi)).toReal / k) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (2 / Real.pi) * ((eVariationOn f (Icc (-1 : ℝ) 1)).toReal / k) := by gcongr
    _ = _ := by ring

/-- The full BV coefficient bound for an AC derivative chain, with exact degree shifts.
Source: Trefethen, ATAP, Thm 7.1; focused reroutes, Theorem `thm:bvcoef`.
`F j` is the specified derivative representative; `F (j+1)=deriv (F j)` is required
almost everywhere on `[-1,1]`. This includes `ν=0` and `V=0`.
atlas: chebyshev-coeff-bv-decay -/
theorem abs_chebyshevCoeff_le_descFactorial {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V)
    {k : ℕ} (hk : ν + 1 ≤ k) :
    |chebyshevCoeff (F 0) k| ≤ 2 * V / (Real.pi * (k.descFactorial (ν + 1) : ℝ)) := by
  induction ν generalizing F k with
  | zero =>
      have hb := abs_chebyshevCoeff_le_variation_div hBV (by omega : 0 < k)
      simp only [Nat.zero_add, Nat.descFactorial_one] at *
      exact hb.trans (by gcongr)
  | succ ν ih =>
      have hu : AbsolutelyContinuousOnInterval (F 0) (-1) 1 := hAC 0 (by omega)
      have hv : BoundedVariationOn (F 1) (Icc (-1 : ℝ) 1) := by
        by_cases hν : ν = 0
        · simpa [hν] using hBV
        · have h := (hAC 1 (by omega)).boundedVariationOn
          simpa using h
      have hshiftAC : ∀ j < ν, AbsolutelyContinuousOnInterval (fun x => F (j + 1) x) (-1) 1 :=
        fun j hj => hAC (j + 1) (by omega)
      have hshiftder : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 →
          deriv (fun t => F (j + 1) t) x = F ((j + 1) + 1) x :=
        fun j hj => hderiv (j + 1) (by omega)
      have hl := ih (F := fun j => F (j + 1)) hshiftAC hshiftder hBV hV
        (k := k - 1) (by omega)
      have hr := ih (F := fun j => F (j + 1)) hshiftAC hshiftder hBV hV
        (k := k + 1) (by omega)
      have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
      have hDpos : 0 < ((k - 1).descFactorial (ν + 1) : ℝ) := by
        exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : ν + 1 ≤ k - 1))
      have hDle : ((k - 1).descFactorial (ν + 1) : ℝ) ≤
          ((k + 1).descFactorial (ν + 1) : ℝ) := by
        exact_mod_cast Nat.descFactorial_le (ν + 1) (show k - 1 ≤ k + 1 by omega)
      have hr' : |chebyshevCoeff (F 1) (k + 1)| ≤
          2 * V / (Real.pi * ((k - 1).descFactorial (ν + 1) : ℝ)) := by
        exact hr.trans (div_le_div_of_nonneg_left (by positivity)
          (mul_pos pi_pos hDpos) (mul_le_mul_of_nonneg_left hDle pi_pos.le))
      have hkreal : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hfactor : (k.descFactorial (ν + 1 + 1) : ℝ) =
          (k : ℝ) * ((k - 1).descFactorial (ν + 1) : ℝ) := by
        have hn := Nat.succ_descFactorial_succ (k - 1) (ν + 1)
        have hkm : k - 1 + 1 = k := by omega
        rw [hkm] at hn
        exact_mod_cast hn
      rw [chebyshevCoeff_eq_sub_derivative hu (hderiv 0 (by omega)) hv (by omega),
        abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hkreal)]
      calc
        _ ≤ (|chebyshevCoeff (F 1) (k - 1)| + |chebyshevCoeff (F 1) (k + 1)|) / (2 * k) :=
          div_le_div_of_nonneg_right (abs_sub _ _) (by positivity)
        _ ≤ (2 * V / (Real.pi * ((k - 1).descFactorial (ν + 1) : ℝ)) +
            2 * V / (Real.pi * ((k - 1).descFactorial (ν + 1) : ℝ))) / (2 * k) := by
          exact div_le_div_of_nonneg_right (add_le_add hl hr') (by positivity)
        _ = _ := by rw [hfactor]; ring

end NLAlib

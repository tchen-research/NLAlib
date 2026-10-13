import NLAlib.ForMathlib.Analysis.BoundedVariationIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Cosine coefficient bounds for bounded variation

Ordinary interval integration and a bounded sine primitive give the exact
`V/k` bound used by `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Real Set MeasureTheory

namespace NLAlib

/-- Cosine substitution does not increase variation on the standard half period.
Source: monotone reparametrization of variation; helper for `chebyshev-coeff-bv-decay`. -/
theorem variationOn_comp_cos_le (h : ℝ → ℝ) :
    eVariationOn (h ∘ cos) (Icc (0 : ℝ) Real.pi) ≤ eVariationOn h (Icc (-1 : ℝ) 1) :=
  eVariationOn.comp_le_of_antitoneOn h cos strictAntiOn_cos.antitoneOn
    (fun x _ => ⟨neg_one_le_cos x, cos_le_one x⟩)

/-- Cosine substitution preserves bounded variation.
Source: monotone reparametrization of variation; helper for `chebyshev-coeff-bv-decay`. -/
theorem boundedVariationOn_comp_cos {h : ℝ → ℝ}
    (hh : BoundedVariationOn h (Icc (-1 : ℝ) 1)) :
    BoundedVariationOn (h ∘ cos) (Icc (0 : ℝ) Real.pi) :=
  ((variationOn_comp_cos_le h).trans_lt hh.lt_top).ne

/-- The `k`-th oscillatory cosine integral of a BV function is bounded by `V/k`.
Source: focused reroutes, Lemma `lem:bvbase`; no Stieltjes integral is needed.
Helper for `chebyshev-coeff-bv-decay`. -/
theorem abs_integral_mul_cos_le_variation_div {h : ℝ → ℝ}
    (hh : BoundedVariationOn h (Icc (0 : ℝ) Real.pi)) {k : ℕ} (hk : 0 < k) :
    |∫ θ in 0..Real.pi, h θ * cos ((k : ℝ) * θ)| ≤
      (eVariationOn h (Icc (0 : ℝ) Real.pi)).toReal / k := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hder : ∀ θ : ℝ, HasDerivAt (fun t => sin ((k : ℝ) * t) / k)
      (cos ((k : ℝ) * θ)) θ := by
    intro θ
    simpa [Function.comp_def, hkpos.ne'] using
      ((hasDerivAt_sin ((k : ℝ) * θ)).comp θ
        ((hasDerivAt_id θ).const_mul (k : ℝ))).div_const (k : ℝ)
  have hbound := abs_integral_mul_le_primitive_bound_mul_variation
    (G := fun θ => sin ((k : ℝ) * θ) / k) (B := 1) (M := 1 / (k : ℝ))
    Real.pi_pos hh (by fun_prop) zero_le_one (by positivity)
    (fun θ _ => abs_cos_le_one _)
    (fun θ _ => by
      rw [abs_div, abs_of_pos hkpos]
      exact div_le_div_of_nonneg_right (abs_sin_le_one _) hkpos.le)
    (by simp) (by rw [sin_nat_mul_pi]; simp) (fun θ _ => hder θ)
  simpa only [one_div, mul_one, mul_comm, div_eq_mul_inv] using hbound

end NLAlib

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Ring

/-!
# Endpoint comparison from a power-weighted derivative estimate

Only interior differentiability is needed; this is suitable for expectations
along square-root interpolations whose endpoints are known by continuity.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace Real

/-- A power-weighted derivative bound controls the difference of endpoint
powers. Positivity is only required on the closed comparison interval, and
the actual derivatives are required only on its interior. -/
theorem abs_rpow_sub_rpow_le_of_hasDerivAt_bound
    {f f' : ℝ → ℝ} {a b s K : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    (hf : ContinuousOn f (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < f x)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo a b, |f' x| ≤ K * f x ^ (1 - s)) :
    |f b ^ s - f a ^ s| ≤ (s * K) * (b - a) := by
  by_cases hlt : a < b
  · have hg : ContinuousOn (fun x => f x ^ s) (Icc a b) :=
      hf.rpow_const (fun x hx => Or.inl (hpos x hx).ne')
    have hgd : ∀ x ∈ Ioo a b,
        HasDerivAt (fun t => f t ^ s) (f' x * s * f x ^ (s - 1)) x := by
      intro x hx
      exact (hderiv x hx).rpow_const (Or.inl (hpos x (Ioo_subset_Icc_self hx)).ne')
    have hgb : ∀ x ∈ Ioo a b, |f' x * s * f x ^ (s - 1)| ≤ s * K := by
      intro x hx
      have hpx := hpos x (Ioo_subset_Icc_self hx)
      rw [abs_mul, abs_mul, abs_of_nonneg hs,
        abs_of_nonneg (rpow_nonneg hpx.le _)]
      calc
        |f' x| * s * f x ^ (s - 1) ≤ (K * f x ^ (1 - s)) * s * f x ^ (s - 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hbound x hx) hs) (rpow_nonneg hpx.le _)
        _ = (s * K) * (f x ^ (1 - s) * f x ^ (s - 1)) := by ring
        _ = s * K := by
          rw [← rpow_add hpx, show 1 - s + (s - 1) = 0 by ring, rpow_zero, mul_one]
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
      (fun x => f x ^ s) (fun x => f' x * s * f x ^ (s - 1)) hlt hg hgd
    have hb := hgb c hc
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr hlt)] at hb
    exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hb
  · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    simp

end Real

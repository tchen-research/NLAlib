import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Log-convexity of the first three positive moments

Integrating `f (f-c)^2 ≥ 0` proves the moment Cauchy--Schwarz inequality
without requiring a square-root integrability interface.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace MeasureTheory

/-- The first three finite moments of a nonnegative real function satisfy
the moment Cauchy--Schwarz inequality, including zero first moment. -/
theorem sq_integral_sq_le_integral_mul_integral_cube
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (h1 : Integrable f μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) (h3 : Integrable (fun x => f x ^ 3) μ) :
    (∫ x, f x ^ 2 ∂μ) ^ 2 ≤ (∫ x, f x ∂μ) * (∫ x, f x ^ 3 ∂μ) := by
  have hnonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hf
  rcases eq_or_lt_of_le hnonneg with hz | hp
  · have hfzero : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hf h1).mp hz.symm
    have h2zero : (fun x => f x ^ 2) =ᵐ[μ] 0 := hfzero.mono fun x hx => by simp [hx]
    rw [integral_congr_ae h2zero]
    simp only [Pi.zero_apply, integral_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ← hz,
      zero_mul, le_refl]
  · let c : ℝ := (∫ x, f x ^ 2 ∂μ) / (∫ x, f x ∂μ)
    have hc : (∫ x, f x ∂μ) * c = ∫ x, f x ^ 2 ∂μ :=
      mul_div_cancel₀ _ hp.ne'
    have hpoly : 0 ≤ ∫ x, f x ^ 3 - (2 * c) * f x ^ 2 + c ^ 2 * f x ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hf] with x hx
      change 0 ≤ f x at hx
      change 0 ≤ f x ^ 3 - (2 * c) * f x ^ 2 + c ^ 2 * f x
      have he : f x ^ 3 - (2 * c) * f x ^ 2 + c ^ 2 * f x = f x * (f x - c) ^ 2 := by ring
      rw [he]
      exact mul_nonneg hx (sq_nonneg _)
    have hadd := integral_add (h3.sub (h2.const_mul (2 * c))) (h1.const_mul (c ^ 2))
    have hsub := integral_sub h3 (h2.const_mul (2 * c))
    simp only [Pi.sub_apply] at hadd
    rw [hadd, hsub, integral_const_mul, integral_const_mul] at hpoly
    have hc2 := congrArg (fun x : ℝ => c * x) hc
    have hbound : c ^ 2 * (∫ x, f x ∂μ) ≤ ∫ x, f x ^ 3 ∂μ := by nlinarith only [hpoly, hc2]
    calc
      (∫ x, f x ^ 2 ∂μ) ^ 2 = ((∫ x, f x ∂μ) * c) ^ 2 := congrArg (fun x : ℝ => x ^ 2) hc.symm
      _ = (∫ x, f x ∂μ) * (c ^ 2 * (∫ x, f x ∂μ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound hnonneg

end MeasureTheory

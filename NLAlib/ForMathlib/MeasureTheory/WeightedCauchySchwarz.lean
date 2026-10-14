import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted Cauchy--Schwarz for real integrals

A finite weighted-square proof using the discriminant of the integral of
`(f-c)^2*w`. It needs integrability of the three quantities in the statement,
and does not install an `L²` structure on the functions.
-/

noncomputable section
namespace MeasureTheory

/-- Cauchy--Schwarz for two real functions, expressed with their actual square
integrals and product integral. Source: the finite quadratic discriminant proof. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : Integrable (fun x => (f x)^2) μ) (hg : Integrable (fun x => (g x)^2) μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ) * ∫ x, (g x)^2 ∂μ := by
  have hquad (c : ℝ) : 0 ≤ (∫ x, (g x)^2 ∂μ) * (c*c) +
      (-2 * ∫ x, f x * g x ∂μ) * c + ∫ x, (f x)^2 ∂μ := by
    have hnonneg : 0 ≤ ∫ x, (f x - c*g x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have heq : (fun x => (f x - c*g x)^2) =
        (fun x => (f x)^2 - (2*c) * (f x * g x) + (c*c) * (g x)^2) := by
      funext x
      ring
    rw [heq] at hnonneg
    have hadd := integral_add (hf.sub (hfg.const_mul (2*c))) (hg.const_mul (c*c))
    simp only [Pi.sub_apply] at hadd
    rw [hadd, integral_sub hf (hfg.const_mul (2*c)), integral_const_mul,
      integral_const_mul] at hnonneg
    nlinarith
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith

/-- The weighted square of an integral is bounded by the weighted square norm
times the total weight. Source: Cauchy--Schwarz, finite quadratic proof. -/
theorem sq_integral_mul_le_integral_sq_mul_mul_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f w : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hf : Integrable (fun x => f x * w x) μ)
    (hsq : Integrable (fun x => (f x)^2 * w x) μ) (hwi : Integrable w μ) :
    (∫ x, f x * w x ∂μ)^2 ≤ (∫ x, (f x)^2 * w x ∂μ) * ∫ x, w x ∂μ := by
  have hquad (c : ℝ) : 0 ≤ (∫ x, w x ∂μ) * (c*c) +
      (-2 * ∫ x, f x * w x ∂μ) * c + ∫ x, (f x)^2 * w x ∂μ := by
    have hnonneg : 0 ≤ ∫ x, (f x - c)^2 * w x ∂μ :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)
    have heq : (fun x => (f x - c)^2 * w x) =
        (fun x => (f x)^2 * w x - (2*c) * (f x * w x) + (c*c) * w x) := by
      funext x
      ring
    rw [heq] at hnonneg
    have hadd := integral_add (hsq.sub (hf.const_mul (2*c))) (hwi.const_mul (c*c))
    simp only [Pi.sub_apply] at hadd
    rw [hadd, integral_sub hsq (hf.const_mul (2*c)), integral_const_mul,
      integral_const_mul] at hnonneg
    nlinarith
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith

end MeasureTheory

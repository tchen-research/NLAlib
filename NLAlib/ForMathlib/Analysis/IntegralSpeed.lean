import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating a square-root speed bound

The native displacement-versus-speed theorem only needs continuity at the
endpoints and differentiability on the open interval. The exact integral of
(3/2)sqrt(t) on [0,1] is one, preserving the Cauchy comparison constant.
-/

noncomputable section
open MeasureTheory Set
namespace NLAlib
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous path with speed at most (3/2)sqrt(t) C on (0,1) has
endpoint displacement at most C, with no endpoint derivative assumption. -/
theorem norm_sub_le_of_norm_deriv_le_sqrt
    (u : ℝ → F) (v : ℝ → F) (hu : ContinuousOn u (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u (v t) t)
    (C : ℝ) (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ‖v t‖ ≤ (3/2) * Real.sqrt t * C) :
    ‖u 1-u 0‖ ≤ C := by
  have hi : IntervalIntegrable (fun t : ℝ => (3/2) * Real.sqrt t * C) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (3/2) * Real.sqrt t * C)).intervalIntegrable 0 1
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hu
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun t ht => by rw [(hd t ht).deriv]; exact hbound t ht) hi
  have he : (∫ t in (0 : ℝ)..1, (3/2) * Real.sqrt t * C) = C := by
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
    simp_rw [Real.sqrt_eq_rpow]
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < 1/2 by norm_num))]
    norm_num
  rwa [he] at h

end NLAlib

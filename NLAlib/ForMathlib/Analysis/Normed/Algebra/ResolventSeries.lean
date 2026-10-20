import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A genuine Neumann expansion for a perturbed algebraic resolvent

The perturbation is multiplied on its actual side. No factors are commuted.
These generic prerequisites will support the ordered matrix-word expansion.
-/

noncomputable section
set_option autoImplicit false
open scoped Ring

namespace spectrum

section Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

private theorem resolvent_add_factor {a h : A} {z : R}
    (hz : z ∈ resolventSet R a) :
    algebraMap R A z - (a + h) =
      (algebraMap R A z - a) * (1 - resolvent a z * h) := by
  have hu : IsUnit (algebraMap R A z - a) := hz
  rw [mul_sub, mul_one, ← mul_assoc]
  change _ = _ - ((algebraMap R A z - a) * (algebraMap R A z - a)⁻¹ʳ) * h
  rw [Ring.mul_inverse_cancel _ hu, one_mul]
  abel

/-- The actual perturbation factorization of the native total resolvent.
Only the original shifted element needs to be a unit for this identity. -/
theorem resolvent_add_eq_inverse_mul {a h : A} {z : R}
    (hz : z ∈ resolventSet R a) :
    resolvent (a + h) z = (1 - resolvent a z * h)⁻¹ʳ * resolvent a z := by
  have hu : IsUnit (algebraMap R A z - a) := hz
  change (algebraMap R A z - (a + h))⁻¹ʳ = _
  rw [resolvent_add_factor hz, Ring.inverse_mul (Or.inl hu)]
  rfl

end Ring

section Normed

variable {R A : Type*} [CommSemiring R] [NormedRing A] [Algebra R A]
  [CompleteSpace A]

/-- A norm-small perturbation yields the literal ordered Neumann series of
the perturbed resolvent, without assuming the desired inverse expansion. -/
theorem hasSum_resolvent_add_of_norm_mul_lt_one {a h : A} {z : R}
    (hz : z ∈ resolventSet R a) (hsmall : ‖resolvent a z * h‖ < 1) :
    HasSum (fun k : ℕ => (resolvent a z * h) ^ k * resolvent a z)
      (resolvent (a + h) z) := by
  rw [resolvent_add_eq_inverse_mul hz]
  exact (hasSum_geom_series_inverse (resolvent a z * h) hsmall).mul_right _

omit [CompleteSpace A] in
/-- The same actual Neumann series is absolutely summable, so it can be
multiplied with other ordered series and observed by continuous linear maps. -/
theorem summable_norm_resolvent_add_series {a h : A} {z : R}
    (hsmall : ‖resolvent a z * h‖ < 1) :
    Summable (fun k : ℕ => ‖(resolvent a z * h) ^ k * resolvent a z‖) := by
  exact ((summable_norm_geometric_of_norm_lt_one hsmall).mul_right
    ‖resolvent a z‖).of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_mul_le _ _)

end Normed

end spectrum

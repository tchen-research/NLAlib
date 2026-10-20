import NLAlib.ForMathlib.Algebra.Resolvent
import Mathlib.Tactic.NoncommRing

/-!
# The commutator of an actual algebraic resolvent

The usual inverse commutator identity holds whenever the parameter lies in
the genuine resolvent set, including algebras with a trivial underlying ring.
-/

noncomputable section
set_option autoImplicit false

/-- The commutator with a genuine resolvent is the resolvent sandwich of
the commutator with the original algebra element. -/
theorem spectrum.mul_resolvent_sub_resolvent_mul
    {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a b : A) {z : R} (hz : z ∈ resolventSet R a) :
    b * resolvent a z - resolvent a z * b =
      resolvent a z * (b * a - a * b) * resolvent a z := by
  have hleft : resolvent a z * (algebraMap R A z - a) = 1 := Ring.inverse_mul_cancel _ hz
  have hright : (algebraMap R A z - a) * resolvent a z = 1 := Ring.mul_inverse_cancel _ hz
  have he : (algebraMap R A z - a) * b - b * (algebraMap R A z - a) = b * a - a * b := by
    rw [sub_mul, mul_sub, (Algebra.commute_algebraMap_left z b).eq]
    abel
  calc
    _ = (resolvent a z * (algebraMap R A z - a)) * b * resolvent a z -
        resolvent a z * b * ((algebraMap R A z - a) * resolvent a z) := by
      rw [hleft, hright, one_mul, mul_one]
    _ = resolvent a z * ((algebraMap R A z - a) * b - b * (algebraMap R A z - a)) *
        resolvent a z := by noncomm_ring
    _ = _ := by rw [he]

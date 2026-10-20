import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute

/-!
# Commutation and adjoints of total algebraic resolvents

The native total resolvent commutes with itself at different scalar parameters
and respects the star operation. These algebraic identities also hold at
spectral parameters where the total inverse is zero.
-/

noncomputable section

/-- Native total resolvents of the same algebra element commute at every pair
of scalar parameters. This follows from centrality of the scalar algebra map
and commutation of total ring inverses. -/
theorem commute_resolvent {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a : A) (r s : R) : Commute (resolvent a r) (resolvent a s) := by
  dsimp only [resolvent]
  apply Commute.ringInverse_ringInverse
  exact (Algebra.commute_algebraMap_left r _).sub_left
    ((Algebra.commute_algebraMap_right s a).sub_right (Commute.refl a))

/-- The star of the native total resolvent is the resolvent of the starred
element at the starred scalar, without an invertibility assumption. -/
theorem star_resolvent {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [InvolutiveStar R] [StarRing A] [StarModule R A] (a : A) (r : R) :
    star (resolvent a r) = resolvent (star a) (star r) := by
  simp only [resolvent, ← Ring.inverse_star, Algebra.algebraMap_eq_smul_one,
    star_sub, star_smul, star_one]

/-- The first resolvent identity at two actual resolvent-set parameters,
including algebras with a trivial underlying ring. -/
theorem spectrum.resolvent_sub_resolvent_eq_sub_smul_mul
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a : A) {z w : R} (hz : z ∈ resolventSet R a) (hw : w ∈ resolventSet R a) :
    resolvent a z - resolvent a w = (w-z) • (resolvent a z * resolvent a w) := by
  have hi : resolvent a z * (algebraMap R A z-a) = 1 := Ring.inverse_mul_cancel _ hz
  have hj : (algebraMap R A w-a) * resolvent a w = 1 := Ring.mul_inverse_cancel _ hw
  have he : (algebraMap R A w-a)-(algebraMap R A z-a) = (w-z) • (1 : A) := by
    rw [sub_smul, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
    abel
  calc
    _ = resolvent a z * ((algebraMap R A w-a)-(algebraMap R A z-a)) *
        resolvent a w := by
      rw [mul_sub, sub_mul, mul_assoc, hj, hi, mul_one, one_mul]
    _ = _ := by rw [he, mul_smul_comm, mul_one, smul_mul_assoc]

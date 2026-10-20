import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Transport of resolvents by algebra homomorphisms

At a genuine resolvent parameter, a unital algebra map sends the inverse to
the inverse of its image. Injectivity and inverse-closedness of the map are
unnecessary. This applies in particular to the actual coefficient embedding
on a Hilbert direct sum.
-/

noncomputable section
set_option autoImplicit false

variable {R A B : Type*} [CommSemiring R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]

/-- A unital algebra homomorphism transports the actual resolvent at every
parameter where the original scalar shift is a unit. -/
theorem AlgHom.map_resolvent (φ : A →ₐ[R] B) {a : A} {z : R}
    (hz : z ∈ resolventSet R a) :
    φ (resolvent a z) = resolvent (φ a) z := by
  change IsUnit (algebraMap R A z - a) at hz
  obtain ⟨u, hu⟩ := hz
  have hmap : (φ (u : A)) = algebraMap R B z - φ a := by
    rw [hu, map_sub, φ.commutes]
  change φ (Ring.inverse (algebraMap R A z - a)) =
    Ring.inverse (algebraMap R B z - φ a)
  rw [← hu, Ring.inverse_unit, ← hmap]
  change φ ((u⁻¹ : Aˣ) : A) = Ring.inverse (((Units.map φ.toMonoidHom u : Bˣ) : B))
  rw [Ring.inverse_unit]
  rfl

end

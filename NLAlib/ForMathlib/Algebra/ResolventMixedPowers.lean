import NLAlib.ForMathlib.Algebra.Resolvent
import Mathlib.Tactic.NoncommRing

/-!
# A finite recursion for actual mixed resolvent powers

The first resolvent identity reduces mixed powers at two parameters to
two terms of lower total degree. This includes trivial algebras and does
not require a chosen spectral decomposition or a partial-fraction premise.
-/

noncomputable section
set_option autoImplicit false
namespace spectrum

/-- The actual two-parameter mixed resolvent power satisfies its lower-degree recursion. -/
theorem sub_smul_resolvent_pow_mul_pow
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a : A) {z w : R} (hz : z∈resolventSet R a) (hw : w∈resolventSet R a)
    (p q : ℕ) :
    (w-z)•(resolvent a z^(p+1)*resolvent a w^(q+1))=
      resolvent a z^(p+1)*resolvent a w^q-
        resolvent a z^p*resolvent a w^(q+1) := by
  calc
    _ = resolvent a z^p*((w-z)•(resolvent a z*resolvent a w))*resolvent a w^q := by
      rw [pow_succ (resolvent a z),pow_succ' (resolvent a w)]
      simp only [smul_mul_assoc,mul_smul_comm,mul_assoc]
    _ = resolvent a z^p*(resolvent a z-resolvent a w)*resolvent a w^q := by
      rw [← resolvent_sub_resolvent_eq_sub_smul_mul a hz hw]
    _ = _ := by
      rw [pow_succ (resolvent a z),pow_succ' (resolvent a w)]
      noncomm_ring

end spectrum

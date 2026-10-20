import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Native nonreal resolvents of self-adjoint elements

Complex continuous functional calculus identifies the native total algebraic
resolvent with its scalar inverse function on the actual spectrum. This gives
the sharp reciprocal-height norm bound in every complex C*-algebra, including
the trivial algebra. Consequently no nonzero-Hilbert-space assumption is
needed for bounded operators or finite Hilbert direct sums.

These generic deterministic facts are prerequisites for the mean-uniform
resolvent compression of arXiv:2406.11453v2, Proposition 4.8; no free law or
resolvent comparison is assumed.
-/

noncomputable section
set_option autoImplicit false

open scoped ContinuousFunctionalCalculus

section Algebra

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

private theorem im_eq_zero_of_mem_selfAdjoint_spectrum {a : A}
    (ha : IsSelfAdjoint a) {x : ℂ} (hx : x ∈ spectrum ℂ a) : x.im = 0 := by
  have hxreal : (x.re : ℂ) = x := ha.spectrumRestricts.rightInvOn hx
  rw [← hxreal]
  rfl

private theorem sub_ne_zero_of_mem_selfAdjoint_spectrum {a : A}
    (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0)
    {x : ℂ} (hx : x ∈ spectrum ℂ a) : z - x ≠ 0 := by
  intro heq
  apply hz
  rw [sub_eq_zero.mp heq]
  exact im_eq_zero_of_mem_selfAdjoint_spectrum ha hx

/-- Every nonreal scalar shift of a self-adjoint element is a unit, without
assuming the ambient algebra is nontrivial. -/
theorem IsSelfAdjoint.isUnit_algebraMap_sub_of_im_ne_zero {a : A}
    (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ A z - a) := by
  have hf : ContinuousOn (fun x : ℂ => z - x) (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn
  have hunit : IsUnit (cfc (fun x : ℂ => z - x) a) :=
    (isUnit_cfc_iff _ _ hf ha.isStarNormal).mpr
      (fun _ hx => sub_ne_zero_of_mem_selfAdjoint_spectrum ha hz hx)
  simpa only [cfc_sub (fun _ : ℂ => z) (fun x : ℂ => x) a
    continuous_const.continuousOn continuous_id.continuousOn,
    cfc_const z a ha.isStarNormal, cfc_id' ℂ a ha.isStarNormal]
    using hunit

/-- The native total `resolvent`, whose inverse is `Ring.inverse`, agrees
exactly with complex continuous functional calculus at nonreal height. -/
theorem IsSelfAdjoint.resolvent_eq_cfc_of_im_ne_zero {a : A}
    (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0) :
    resolvent a z = cfc (fun x : ℂ => (z - x)⁻¹) a := by
  have hf : ContinuousOn (fun x : ℂ => z - x) (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn
  have hshift : cfc (fun x : ℂ => z - x) a = algebraMap ℂ A z - a := by
    rw [cfc_sub (fun _ : ℂ => z) (fun x : ℂ => x) a
      continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const z a ha.isStarNormal, cfc_id' ℂ a ha.isStarNormal]
  change Ring.inverse (algebraMap ℂ A z - a) = _
  rw [← hshift]
  exact (cfc_inv (fun x : ℂ => z - x) a
    (fun _ hx => sub_ne_zero_of_mem_selfAdjoint_spectrum ha hz hx) hf ha.isStarNormal).symm

end Algebra

section Norm

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [IsometricContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- A self-adjoint element's native nonreal resolvent has norm at most the
reciprocal absolute imaginary height. The statement includes the trivial
algebra and hence the zero Hilbert space; no `NormOneClass` or nontriviality
premise is imposed. -/
theorem IsSelfAdjoint.norm_resolvent_le {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) : ‖resolvent a z‖ ≤ |z.im|⁻¹ := by
  rw [ha.resolvent_eq_cfc_of_im_ne_zero hz]
  apply norm_cfc_le (inv_nonneg.mpr (abs_nonneg _))
  intro x hx
  rw [norm_inv]
  have hheight : |z.im| ≤ ‖z - x‖ := by
    simpa only [Complex.sub_im, im_eq_zero_of_mem_selfAdjoint_spectrum ha hx,
      sub_zero] using Complex.abs_im_le_norm (z - x)
  simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr hz) hheight

end Norm

end

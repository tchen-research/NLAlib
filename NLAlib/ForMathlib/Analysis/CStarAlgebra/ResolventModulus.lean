import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The actual C*-algebra modulus of a self-adjoint resolvent

Complex and real continuous functional calculus identify the modulus of
the native resolvent with its real scalar modulus on the original spectrum.
This is the deterministic functional-calculus bridge used in the resolvent
ultracontractivity proof of arXiv:2406.11453v2, Theorem 4.2.
-/

noncomputable section
set_option autoImplicit false

open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realResolventCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realResolventCFC

/-- The genuine noncommutative modulus of the native resolvent is the
real continuous functional calculus of the scalar inverse-distance function. -/
theorem IsSelfAdjoint.abs_resolvent_eq_cfc {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) :
    CFC.abs (resolvent a z) = cfc (fun x : ℝ => ‖(z - (x : ℂ))⁻¹‖) a := by
  have hf : ContinuousOn (fun x : ℂ => (z - x)⁻¹) (spectrum ℂ a) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro x hx hzero
    have hxreal := ha.spectrumRestricts.rightInvOn hx
    apply hz
    have hzx : z = x := sub_eq_zero.mp hzero
    rw [hzx, ← hxreal]
    rfl
  rw [ha.resolvent_eq_cfc_of_im_ne_zero hz]
  rw [CFC.abs_eq_cfcₙ_coe_norm ℂ _ (cfc_predicate _ _)]
  calc
    _ = cfc (fun w : ℂ => (‖w‖ : ℂ)) (cfc (fun x : ℂ => (z - x)⁻¹) a) :=
      cfcₙ_eq_cfc (f := fun w : ℂ => (‖w‖ : ℂ))
        (a := cfc (fun x : ℂ => (z - x)⁻¹) a)
        (Complex.continuous_ofReal.comp continuous_norm |>.continuousOn) (by simp)
    _ = cfc (fun x : ℂ => (‖(z - x)⁻¹‖ : ℂ)) a :=
      (cfc_comp' (fun w : ℂ => (‖w‖ : ℂ)) (fun x : ℂ => (z - x)⁻¹) a
        (Complex.continuous_ofReal.comp continuous_norm |>.continuousOn) hf ha.isStarNormal).symm
    _ = _ := cfc_complex_eq_real a (fun x hx => by simp) ha

/-- The scalar modulus calculus preserves the actual resolvent norm. -/
theorem IsSelfAdjoint.norm_cfc_resolvent_modulus {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖cfc (fun x : ℝ => ‖(z - (x : ℂ))⁻¹‖) a‖ = ‖resolvent a z‖ := by
  rw [← ha.abs_resolvent_eq_cfc hz, CFC.norm_abs]

end

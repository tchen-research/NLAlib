import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import NLAlib.ForMathlib.Analysis.Complex.ResolventClamp

/-!
# Actual continuous-functional-calculus clipping of a deterministic mean

The continuous interval projection is applied to the original deterministic
element. Its norm is bounded by the clip radius, and the original/clipped
reference resolvents differ by at most the reciprocal radius at imaginary
height. No spectral projection of the perturbed free operator is needed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

private theorem realClampCFC : IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)

attribute [local instance] realClampCFC

/-- The native continuous interval projection of a self-adjoint element to
the symmetric interval. The total calculus gives zero on other elements. -/
def cfcSymmetricClamp (L : ℝ) (a : A) : A :=
  cfc (fun x : ℝ => max (-L) (min L x)) a

/-- The actual clipped element is self-adjoint. -/
theorem isSelfAdjoint_cfcSymmetricClamp (L : ℝ) (a : A) :
    IsSelfAdjoint (cfcSymmetricClamp L a) := IsSelfAdjoint.cfc

/-- The native actual clipped reference has norm at most the clip radius,
including zero radius and the trivial algebra. -/
theorem norm_cfcSymmetricClamp_le (L : ℝ) (hL : 0≤L) (a : A) :
    ‖cfcSymmetricClamp L a‖ ≤ L := by
  apply norm_cfc_le hL
  intro x hx
  have hp := (Set.projIcc (-L) L (by linarith : -L≤L) x).property
  exact (Real.norm_eq_abs _).trans_le (abs_le.mpr hp)

/-- At purely imaginary height, changing an arbitrary self-adjoint
deterministic reference to its actual clipped version changes its native
resolvent by at most the reciprocal clip radius. -/
theorem IsSelfAdjoint.norm_resolvent_sub_cfcSymmetricClamp_le {a : A}
    (ha : IsSelfAdjoint a) {z : ℂ} (hre : z.re=0) (hz : 0<z.im)
    {L : ℝ} (hL : 0<L) :
    ‖resolvent a z-resolvent (cfcSymmetricClamp L a) z‖ ≤ L⁻¹ := by
  let g : ℂ → ℂ := fun w => ((max (-L) (min L w.re) : ℝ) : ℂ)
  let f : ℂ → ℂ := fun w => (z-w)⁻¹
  have hg : Continuous g := Complex.continuous_ofReal.comp
    (continuous_const.max (continuous_const.min Complex.continuous_re))
  have hne (w : ℂ) (hw : w ∈ spectrum ℂ a) : z-w≠0 := by
    intro hh
    have hreal := ha.spectrumRestricts.rightInvOn hw
    apply hz.ne'
    rw [sub_eq_zero.mp hh,← hreal]
    rfl
  have hf : ContinuousOn f (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ hne
  have hneG (w : ℂ) : z-g w≠0 := by
    intro hh
    apply hz.ne'
    rw [sub_eq_zero.mp hh]
    rfl
  have hfg : ContinuousOn f (g '' spectrum ℂ a) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro w hw
    rcases hw with ⟨v,hv,rfl⟩
    exact hneG v
  have hc : cfcSymmetricClamp L a = cfc g a :=
    cfc_real_eq_complex (fun x : ℝ => max (-L) (min L x)) ha
  have hr : resolvent (cfcSymmetricClamp L a) z =
      cfc (fun w : ℂ => f (g w)) a := by
    calc
      _ = cfc f (cfcSymmetricClamp L a) :=
        (isSelfAdjoint_cfcSymmetricClamp L a).resolvent_eq_cfc_of_im_ne_zero hz.ne'
      _ = cfc f (cfc g a) := congrArg (cfc f) hc
      _ = _ := (cfc_comp' f g a hfg hg.continuousOn ha.isStarNormal).symm
  rw [ha.resolvent_eq_cfc_of_im_ne_zero hz.ne',hr]
  change ‖cfc f a-cfc (fun w : ℂ => f (g w)) a‖ ≤ L⁻¹
  rw [← cfc_sub f (fun w : ℂ => f (g w)) a hf
    (hfg.comp hg.continuousOn (fun _ hx => Set.mem_image_of_mem _ hx))]
  apply norm_cfc_le (inv_nonneg.mpr hL.le)
  intro w hw
  have hreal := ha.spectrumRestricts.rightInvOn hw
  rw [← hreal]
  change ‖(z-(w.re : ℂ))⁻¹-
    (z-((max (-L) (min L w.re) : ℝ) : ℂ))⁻¹‖≤L⁻¹
  exact Complex.norm_inv_sub_real_sub_inv_sub_clamp_le hre hz hL w.re

end

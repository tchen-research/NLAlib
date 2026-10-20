import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# A genuine vector lower bound for a self-adjoint resolvent

Cauchy--Schwarz, the actual inverse identity and normality of the native
resolvent give a lower bound on a unit vector from its actual residual.
This is a scalar Hilbert-space argument, without operator-valued Jensen.
-/

noncomputable section
set_option autoImplicit false
open scoped ComplexOrder ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A genuine self-adjoint resolvent cannot be small on a unit vector
whose actual shifted residual is bounded. Empty Hilbert spaces are
automatically excluded by the unit-vector hypothesis. -/
theorem IsSelfAdjoint.inv_le_norm_resolvent_apply_of_residual_le
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im≠0)
    {u : E} (hu : ‖u‖=1) {L : ℝ} (hL : 0<L)
    (hres : ‖(algebraMap ℂ (E →L[ℂ] E) z-T) u‖≤L) :
    L⁻¹≤‖resolvent T z u‖ := by
  let R := resolvent T z
  let H := algebraMap ℂ (E →L[ℂ] E) z-T
  have hunit : z∈resolventSet ℂ T := hT.isUnit_algebraMap_sub_of_im_ne_zero hz
  have hRH : R*H=1 := Ring.inverse_mul_cancel _ hunit
  have hRu : R (H u)=u := by
    calc
      _ = (R*H) u := rfl
      _ = (1 : E →L[ℂ] E) u := congrArg (fun S : E →L[ℂ] E => S u) hRH
      _ = _ := rfl
  have hnormal : IsStarNormal R := by
    dsimp only [R]
    rw [hT.resolvent_eq_cfc_of_im_ne_zero hz]
    infer_instance
  have hnorm : ‖R.adjoint u‖=‖R u‖ :=
    (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal u).symm
  have hinner : inner ℂ u u=inner ℂ (R.adjoint u) (H u) := by
    rw [R.adjoint_inner_left,hRu]
  have hineq : 1≤‖R u‖*L := by
    calc
      _ = ‖inner ℂ u u‖ := by rw [inner_self_eq_norm_sq_to_K,hu]; norm_num
      _ = ‖inner ℂ (R.adjoint u) (H u)‖ := congrArg norm hinner
      _ ≤ ‖R.adjoint u‖*‖H u‖ := norm_inner_le_norm _ _
      _ ≤ ‖R.adjoint u‖*L := mul_le_mul_of_nonneg_left hres (norm_nonneg _)
      _ = _ := by rw [hnorm]
  simpa only [one_div] using (div_le_iff₀ hL).mpr hineq

end

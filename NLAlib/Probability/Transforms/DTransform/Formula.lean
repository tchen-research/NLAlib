import NLAlib.Probability.Transforms.DTransform.Monotonicity

/-! # Integral-moment formula for the native D-transform logarithmic derivative

This explicit formula supports weak-law continuity of the derivative-based
definition. Source: ScreeNOT, Lemma 8 and Supplement Appendix D.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace NLAlib

/-- The companion transform differentiates as its defining affine combination
of the actual Cauchy transform and the reciprocal evaluation point. -/
theorem hasDerivAt_singularValueCompanionPhi (μ : Measure ℝ) [IsFiniteMeasure μ]
    {γ b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    HasDerivAt (singularValueCompanionPhi μ γ)
      (γ * (dTransformMoment μ 0 y - 2 * y ^ 2 * dTransformMoment μ 1 y) -
        (1 - γ) / y ^ 2) y := by
  have h := ((hasDerivAt_singularValuePhi μ hb hsupport hy).const_mul γ).add
    ((hasDerivAt_inv (ne_of_gt (hb.trans_lt hy))).const_mul (1 - γ))
  convert! h using 1
  ring

/-- Express the actual D-transform root function entirely in terms of its
first two inverse-denominator moments and the actual transforms. -/
theorem singularValuePsi_eq_moments (μ : Measure ℝ) [IsFiniteMeasure μ]
    {γ b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValuePsi μ γ y =
      y * ((dTransformMoment μ 0 y - 2 * y ^ 2 * dTransformMoment μ 1 y) *
          singularValueCompanionPhi μ γ y + singularValuePhi μ y *
          (γ * (dTransformMoment μ 0 y - 2 * y ^ 2 * dTransformMoment μ 1 y) -
            (1 - γ) / y ^ 2)) /
        (singularValuePhi μ y * singularValueCompanionPhi μ γ y) := by
  have hd := (hasDerivAt_singularValuePhi μ hb hsupport hy).mul
    (hasDerivAt_singularValueCompanionPhi (γ := γ) μ hb hsupport hy)
  change HasDerivAt (singularValueDTransform μ γ) _ y at hd
  unfold singularValuePsi
  rw [hd.deriv]
  rfl

end NLAlib

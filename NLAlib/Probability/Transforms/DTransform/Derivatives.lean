import NLAlib.Probability.Transforms.DTransform.Basic
import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Derivatives of actual compact-support D-transforms

Compact-support differentiation is applied only where the denominator is
strictly positive. Source: ScreeNOT, Lemma 8 and Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped Topology
namespace NLAlib

/-- The derivative of an inverse-denominator moment kernel. -/
theorem hasDerivAt_dTransformMoment_kernel (k : ℕ) (y z : ℝ)
    (hden : y ^ 2 - z ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => ((t ^ 2 - z ^ 2)⁻¹) ^ (k + 1))
      (-2 * (k + 1 : ℝ) * y * ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 2)) y := by
  have h := ((((hasDerivAt_id y).pow 2).sub_const (z ^ 2)).inv hden).pow (k + 1)
  convert! h using 1
  simp only [Pi.pow_apply, Pi.inv_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv, inv_pow, pow_add]
  ring

/-- Every inverse-denominator moment differentiates under the actual compact
law. No kernel assumptions outside its support are imposed. -/
theorem hasDerivAt_dTransformMoment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) (k : ℕ) :
    HasDerivAt (dTransformMoment μ k)
      (-2 * (k + 1 : ℝ) * y * dTransformMoment μ (k + 1) y) y := by
  let U : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.2 ^ 2 < p.1 ^ 2}
  let F : ℝ → ℝ → ℝ := fun t z => ((t ^ 2 - z ^ 2)⁻¹) ^ (k + 1)
  let D : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun t z =>
    (-2 * (k + 1 : ℝ) * t * ((t ^ 2 - z ^ 2)⁻¹) ^ (k + 2)) • 1
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (continuous_snd.pow 2) (continuous_fst.pow 2))
  have hden (p : ℝ × ℝ) (hp : p ∈ U) : p.1 ^ 2 - p.2 ^ 2 ≠ 0 :=
    (sub_pos.mpr hp.2).ne'
  have hinv : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 - p.2 ^ 2)⁻¹) U :=
    ((continuous_fst.pow 2).sub (continuous_snd.pow 2)).continuousOn.inv₀ hden
  have hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) U := hinv.pow (k + 1)
  have hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) U :=
    (((continuous_const.mul continuous_fst).continuousOn.mul (hinv.pow (k + 2))).smul
      continuousOn_const)
  have hderiv (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (fun t => F t p.2) (D p.1 p.2) p.1 := by
    convert! (hasDerivAt_dTransformMoment_kernel k p.1 p.2 (hden p hp)).hasFDerivAt using 1
    ext
    simp [D, mul_comm]
  have hpoint (z : ℝ) (hz : z ∈ μ.support) : (y, z) ∈ U :=
    ⟨lt_of_le_of_lt hb hy, sub_pos.mp (dTransform_denominator_pos hb hy (hsupport hz))⟩
  have h := hasFDerivAt_integral_of_compact_support μ
    (μ.isCompact_support_of_subset_Icc hsupport) F D U hU hF hD hderiv y hpoint
  have hDint : (∫ z, D y z ∂μ) =
      (-2 * (k + 1 : ℝ) * y * dTransformMoment μ (k + 1) y) •
        (1 : ℝ →L[ℝ] ℝ) := by
    simp only [D, integral_smul_const, integral_const_mul, dTransformMoment, Nat.add_assoc]
  rw [hDint] at h
  convert! h.hasDerivAt using 1
  simp only [dTransformMoment, smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]

/-- Above the nonnegative support, the actual singular-value transform has
the expected integral derivative. -/
theorem hasDerivAt_singularValuePhi (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    HasDerivAt (singularValuePhi μ)
      (dTransformMoment μ 0 y - 2 * y ^ 2 * dTransformMoment μ 1 y) y := by
  have h := (hasDerivAt_id y).mul (hasDerivAt_dTransformMoment μ hb hsupport hy 0)
  simp only [Nat.cast_zero, zero_add, mul_one] at h
  have he : (fun t => t * dTransformMoment μ 0 t) = singularValuePhi μ :=
    funext fun t => (singularValuePhi_eq_mul_moment μ t).symm
  change HasDerivAt (fun t => t * dTransformMoment μ 0 t)
    (1 * dTransformMoment μ 0 y + y * (-2 * y * dTransformMoment μ 1 y)) y at h
  rw [he] at h
  convert! h using 1
  ring

end NLAlib

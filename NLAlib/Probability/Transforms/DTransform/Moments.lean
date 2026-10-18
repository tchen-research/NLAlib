import NLAlib.Probability.Transforms.DTransform.Basic
import NLAlib.ForMathlib.MeasureTheory.PositiveMomentLogConvex

/-!
# Positive inverse-denominator moments

The actual inverse-denominator moments satisfy the Cauchy--Schwarz inequality
and strict positivity needed for the D-transform root. Source: ScreeNOT,
Supplement Appendix A, expressed without a logarithmic change of variables.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace NLAlib

/-- Inverse-denominator moments are nonnegative above a nonnegative support. -/
theorem dTransformMoment_nonneg (μ : Measure ℝ) {b y : ℝ}
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) (k : ℕ) :
    0 ≤ dTransformMoment μ k y := by
  apply integral_nonneg_of_ae
  filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
  exact (pow_pos (inv_pos.mpr (dTransform_denominator_pos hb hy hz)) (k + 1)).le

/-- Every inverse-denominator moment of an actual probability law is strictly
positive above its support. -/
theorem dTransformMoment_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {b y : ℝ}
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) (k : ℕ) :
    0 < dTransformMoment μ k y := by
  have hn := dTransformMoment_nonneg μ hb hsupport hy k
  by_contra hnot
  have hz : dTransformMoment μ k y = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hp : 0 ≤ᵐ[μ] fun z => ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 1) := by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
    exact (pow_pos (inv_pos.mpr (dTransform_denominator_pos hb hy hz)) (k + 1)).le
  have he := (integral_eq_zero_iff_of_nonneg_ae hp
    (integrable_dTransformMoment_kernel μ hb hsupport hy k)).mp hz
  obtain ⟨z, hzs, hzz⟩ := ((μ.ae_mem_Icc_of_support_subset hsupport).and he).exists
  have hpos := pow_pos (inv_pos.mpr (dTransform_denominator_pos hb hy hzs)) (k + 1)
  change ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 1) = 0 at hzz
  linarith

/-- Cauchy--Schwarz for three successive actual inverse-denominator moments. -/
theorem dTransformMoment_one_sq_le_zero_mul_two (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    dTransformMoment μ 1 y ^ 2 ≤ dTransformMoment μ 0 y * dTransformMoment μ 2 y := by
  have hp : 0 ≤ᵐ[μ] fun z => (y ^ 2 - z ^ 2)⁻¹ := by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
    exact (inv_pos.mpr (dTransform_denominator_pos hb hy hz)).le
  have h1 : Integrable (fun z => (y ^ 2 - z ^ 2)⁻¹) μ := by
    simpa only [zero_add, pow_one] using integrable_dTransformMoment_kernel μ hb hsupport hy 0
  have h2 : Integrable (fun z => ((y ^ 2 - z ^ 2)⁻¹) ^ 2) μ :=
    integrable_dTransformMoment_kernel μ hb hsupport hy 1
  have h3 : Integrable (fun z => ((y ^ 2 - z ^ 2)⁻¹) ^ 3) μ :=
    integrable_dTransformMoment_kernel μ hb hsupport hy 2
  simpa only [dTransformMoment, zero_add, pow_one] using
    sq_integral_sq_le_integral_mul_integral_cube hp h1 h2 h3

/-- Nonzero positive support makes the moment defect strictly positive.
This is the strict part of logarithmic elasticity monotonicity. -/
theorem sq_mul_dTransformMoment_one_sub_zero_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {b y : ℝ}
    (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b) (hbmem : b ∈ μ.support) (hy : b < y) :
    0 < y ^ 2 * dTransformMoment μ 1 y - dTransformMoment μ 0 y := by
  let f : ℝ → ℝ := fun z => z ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2
  have he (z : ℝ) (hz : z ∈ Icc 0 b) :
      y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹ = f z := by
    dsimp [f]
    field_simp [(dTransform_denominator_pos hb.le hy hz).ne']
    ring
  have hae : (fun z => y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹) =ᵐ[μ] f :=
    (μ.ae_mem_Icc_of_support_subset hsupport).mono fun z hz => he z hz
  have hi : Integrable f μ :=
    ((integrable_dTransformMoment_kernel μ hb.le hsupport hy 1).const_mul (y ^ 2) |>.sub
      (by simpa only [zero_add, pow_one] using
        integrable_dTransformMoment_kernel μ hb.le hsupport hy 0)).congr hae
  have hidentity : y ^ 2 * dTransformMoment μ 1 y - dTransformMoment μ 0 y = ∫ z, f z ∂μ := by
    rw [← integral_congr_ae hae]
    rw [integral_sub ((integrable_dTransformMoment_kernel μ hb.le hsupport hy 1).const_mul _)
      (by simpa only [zero_add, pow_one] using
        integrable_dTransformMoment_kernel μ hb.le hsupport hy 0), integral_const_mul]
    simp only [dTransformMoment, zero_add, pow_one]
  rw [hidentity]
  have hn : 0 ≤ ∫ z, f z ∂μ := integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  by_contra hnot
  have hz := (integral_eq_zero_iff_of_nonneg (fun z => mul_nonneg (sq_nonneg z) (sq_nonneg _)) hi).mp
    (le_antisymm (le_of_not_gt hnot) hn)
  have hz0 : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℝ) := by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport, hz] with z hzs hzz
    change z ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 = 0 at hzz
    have hk : ((y ^ 2 - z ^ 2)⁻¹) ^ 2 ≠ 0 :=
      (sq_pos_of_pos (inv_pos.mpr (dTransform_denominator_pos hb.le hy hzs))).ne'
    have hzsq : z ^ 2 = 0 := (mul_eq_zero.mp hzz).resolve_right hk
    simpa only [Set.mem_singleton_iff, sq_eq_zero_iff] using hzsq
  have hs0 : μ.support ⊆ ({0} : Set ℝ) :=
    μ.support_subset_of_isClosed isClosed_singleton hz0
  have hbzero := hs0 hbmem
  simp only [Set.mem_singleton_iff] at hbzero
  linarith

end NLAlib

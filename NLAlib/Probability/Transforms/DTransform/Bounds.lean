import NLAlib.Probability.Transforms.DTransform.Monotonicity

/-!
# Explicit support bounds for D-transform logarithmic derivatives

Elementary kernel inequalities give the limit at infinity and the universal
upper root bracket. Source: ScreeNOT, Lemma 8; the `sqrt(3)` bracket follows
directly from the same compact-support kernels.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace NLAlib

/-- Multiplying the second inverse moment by the squared evaluation point
dominates the first inverse moment. -/
theorem dTransformMoment_zero_le_sq_mul_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    dTransformMoment μ 0 y ≤ y ^ 2 * dTransformMoment μ 1 y := by
  have h0 : Integrable (fun z => (y ^ 2 - z ^ 2)⁻¹) μ := by
    simpa only [zero_add, pow_one] using integrable_dTransformMoment_kernel μ hb hsupport hy 0
  have h1 := (integrable_dTransformMoment_kernel μ hb hsupport hy 1).const_mul (y ^ 2)
  have he := integral_mono_ae h0 h1 (show (fun z => (y ^ 2 - z ^ 2)⁻¹) ≤ᵐ[μ]
      (fun z => y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2) from by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
    have hid : y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹ =
        z ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 := by
      field_simp [(dTransform_denominator_pos hb hy hz).ne']
      ring
    have hp := mul_nonneg (sq_nonneg z) (sq_nonneg ((y ^ 2 - z ^ 2)⁻¹))
    linarith)
  simpa only [integral_const_mul, dTransformMoment, zero_add, pow_one] using he

/-- The positive distance to the support controls the next inverse moment. -/
theorem dTransformMoment_one_le_inv_gap_mul_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    dTransformMoment μ 1 y ≤ (y ^ 2 - b ^ 2)⁻¹ * dTransformMoment μ 0 y := by
  have hgap := dTransform_denominator_pos hb hy (show b ∈ Icc 0 b from ⟨hb, le_rfl⟩)
  have h0 : Integrable (fun z => (y ^ 2 - z ^ 2)⁻¹) μ := by
    simpa only [zero_add, pow_one] using integrable_dTransformMoment_kernel μ hb hsupport hy 0
  have he := integral_mono_ae (integrable_dTransformMoment_kernel μ hb hsupport hy 1)
    (h0.const_mul ((y ^ 2 - b ^ 2)⁻¹)) (show
      (fun z => ((y ^ 2 - z ^ 2)⁻¹) ^ 2) ≤ᵐ[μ]
        (fun z => (y ^ 2 - b ^ 2)⁻¹ * (y ^ 2 - z ^ 2)⁻¹) from by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
    have hden := dTransform_denominator_pos hb hy hz
    have hzb : z ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hz.1 hb).mpr hz.2
    have hk : (y ^ 2 - z ^ 2)⁻¹ ≤ (y ^ 2 - b ^ 2)⁻¹ :=
      (inv_le_inv₀ hden hgap).mpr (by linarith)
    simpa only [pow_two, mul_comm] using
      mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hden.le))
  simpa only [integral_const_mul, dTransformMoment, zero_add, pow_one] using he

/-- The actual logarithmic elasticity lies between two explicit support
bounds. The upper bound is attained by an atom at zero. -/
theorem singularValueElasticity_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    -1 - 2 * b ^ 2 / (y ^ 2 - b ^ 2) ≤ singularValueElasticity μ y ∧
      singularValueElasticity μ y ≤ -1 := by
  have h0 := dTransformMoment_pos μ hb hsupport hy 0
  have hlow := dTransformMoment_zero_le_sq_mul_one μ hb hsupport hy
  have hhigh := dTransformMoment_one_le_inv_gap_mul_zero μ hb hsupport hy
  have hgap := dTransform_denominator_pos hb hy (show b ∈ Icc 0 b from ⟨hb, le_rfl⟩)
  have hl : 1 ≤ y ^ 2 * dTransformMoment μ 1 y / dTransformMoment μ 0 y :=
    (le_div_iff₀ h0).mpr (by simpa only [one_mul] using hlow)
  have hu0 : dTransformMoment μ 1 y / dTransformMoment μ 0 y ≤ (y ^ 2 - b ^ 2)⁻¹ :=
    (div_le_iff₀ h0).mpr hhigh
  have hu : y ^ 2 * dTransformMoment μ 1 y / dTransformMoment μ 0 y ≤
      y ^ 2 / (y ^ 2 - b ^ 2) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_of_nonneg_left hu0 (sq_nonneg y)
  have he : -1 - 2 * b ^ 2 / (y ^ 2 - b ^ 2) = 1 - 2 * (y ^ 2 / (y ^ 2 - b ^ 2)) := by
    field_simp [hgap.ne']
    ring
  rw [singularValueElasticity_eq_moments μ hb hsupport hy, he]
  have he2 : 2 * y ^ 2 * dTransformMoment μ 1 y / dTransformMoment μ 0 y =
      2 * (y ^ 2 * dTransformMoment μ 1 y / dTransformMoment μ 0 y) := by ring
  rw [he2]
  constructor <;> linarith

/-- Uniform elementary bounds for the actual D-transform root function. -/
theorem singularValuePsi_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b y : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    -2 - 4 * b ^ 2 / (y ^ 2 - b ^ 2) ≤ singularValuePsi μ γ y ∧ singularValuePsi μ γ y ≤ -2 := by
  let ν := dTransformCompanionMeasure μ γ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_dTransformCompanionMeasure μ hγ hγ1
  have h := singularValueElasticity_bounds μ hb hsupport hy
  have hn := singularValueElasticity_bounds ν hb (support_dTransformCompanionMeasure_subset μ hb hsupport) hy
  rw [singularValuePsi_eq_add_elasticity μ hγ hγ1 hb hsupport hy]
  change -2 - 4 * b ^ 2 / (y ^ 2 - b ^ 2) ≤
      singularValueElasticity μ y + singularValueElasticity ν y ∧
    singularValueElasticity μ y + singularValueElasticity ν y ≤ -2
  constructor
  · have hl := add_le_add h.1 hn.1
    convert hl using 1 <;> (first | rfl | ring)
  · simpa only [show (-1 : ℝ) + -1 = -2 by norm_num] using add_le_add h.2 hn.2

/-- The universal right endpoint already lies beyond the `-4` crossing.
Source: compact-support kernel bound for the ScreeNOT threshold.
atlas: scree-threshold-root (partial) -/
theorem neg_four_le_singularValuePsi_sqrt_three_mul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b) :
    -4 ≤ singularValuePsi μ γ (Real.sqrt 3 * b) := by
  have hsqrt : 1 < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hy : b < Real.sqrt 3 * b := by nlinarith [mul_lt_mul_of_pos_right hsqrt hb]
  have h := (singularValuePsi_bounds μ hγ hγ1 hb.le hsupport hy).1
  have hs : (Real.sqrt 3 * b) ^ 2 = 3 * b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have he : -2 - 4 * b ^ 2 / ((Real.sqrt 3 * b) ^ 2 - b ^ 2) = -4 := by
    rw [hs]
    field_simp [hb.ne']
    ring
  rwa [he] at h

end NLAlib

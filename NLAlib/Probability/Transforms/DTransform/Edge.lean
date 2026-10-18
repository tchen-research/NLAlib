import NLAlib.Probability.Transforms.DTransform.Bounds
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Real.Sqrt

/-!
# Edge-thickness control of the D-transform logarithmic derivative

Cauchy--Schwarz controls the first edge resolvent by the square root of its
second moment. This supplies the actual edge divergence from the thickness
hypothesis. Source: ScreeNOT, Lemma 8(2), Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace NLAlib

/-- The actual second edge-resolvent moment in the thickness assumption. -/
def singularValueEdgeMoment (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ z, ((y - z)⁻¹) ^ 2 ∂μ

/-- The edge resolvent has every finite second moment above compact support. -/
theorem memLp_two_inv_sub_of_support_subset_Icc (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    MemLp (fun z => (y - z)⁻¹) 2 μ := by
  apply MemLp.of_bound (by fun_prop) ((y - b)⁻¹)
  filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
  have hyz : 0 < y - z := by linarith [hz.2]
  have hyb : 0 < y - b := sub_pos.mpr hy
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyz)]
  exact (inv_le_inv₀ hyz hyb).mpr (by linarith [hz.2])

/-- The singular-value transform is bounded by the first edge resolvent. -/
theorem singularValuePhi_le_integral_inv_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValuePhi μ y ≤ ∫ z, (y - z)⁻¹ ∂μ := by
  have hi : Integrable (fun z => y / (y ^ 2 - z ^ 2)) μ := by
    simpa only [zero_add, pow_one, div_eq_mul_inv] using
      (integrable_dTransformMoment_kernel μ hb hsupport hy 0).const_mul y
  have hk := (memLp_two_inv_sub_of_support_subset_Icc μ hsupport hy).integrable one_le_two
  apply integral_mono_ae hi hk
  filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
  have hyz : 0 < y - z := by linarith [hz.2]
  have hyp : 0 < y + z := by linarith [hz.1]
  have he : y / (y ^ 2 - z ^ 2) = (y / (y + z)) * (y - z)⁻¹ := by
    field_simp [hyz.ne', hyp.ne', (dTransform_denominator_pos hb hy hz).ne']
    ring
  rw [he]
  have hcoeff : y / (y + z) ≤ 1 := (div_le_one hyp).mpr (by linarith [hz.1])
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hyz.le)

/-- The magnitude of the negative transform derivative dominates half the
actual second edge-resolvent moment. -/
theorem div_two_edgeMoment_le_neg_deriv_singularValuePhi
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {b y : ℝ}
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValueEdgeMoment μ y / 2 ≤ -deriv (singularValuePhi μ) y := by
  have h0 : Integrable (fun z => (y ^ 2 - z ^ 2)⁻¹) μ := by
    simpa only [zero_add, pow_one] using integrable_dTransformMoment_kernel μ hb hsupport hy 0
  have h1 := (integrable_dTransformMoment_kernel μ hb hsupport hy 1).const_mul (2 * y ^ 2)
  have hk := (memLp_two_inv_sub_of_support_subset_Icc μ hsupport hy).integrable_sq
  have he : -deriv (singularValuePhi μ) y =
      ∫ z, 2 * y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹ ∂μ := by
    rw [(hasDerivAt_singularValuePhi μ hb hsupport hy).deriv, integral_sub h1 h0, integral_const_mul]
    simp only [dTransformMoment, zero_add, pow_one]
    ring
  rw [he]
  have hle := integral_mono_ae (hk.const_mul (1 / 2 : ℝ)) (h1.sub h0) (show
      (fun z => (1 / 2 : ℝ) * ((y - z)⁻¹) ^ 2) ≤ᵐ[μ]
        (fun z => 2 * y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹) from by
    filter_upwards [μ.ae_mem_Icc_of_support_subset hsupport] with z hz
    have hyz : 0 < y - z := by linarith [hz.2]
    have hyp : 0 < y + z := by linarith [hz.1]
    have hid : 2 * y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹ =
        ((y ^ 2 + z ^ 2) / (y + z) ^ 2) * ((y - z)⁻¹) ^ 2 := by
      field_simp [hyz.ne', hyp.ne', (dTransform_denominator_pos hb hy hz).ne']
      ring
    rw [hid]
    have hcoeff : (1 / 2 : ℝ) ≤ (y ^ 2 + z ^ 2) / (y + z) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hyp)).mpr
      nlinarith [sq_nonneg (y - z)]
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
  change (∫ z, (1 / 2 : ℝ) * ((y - z)⁻¹) ^ 2 ∂μ) ≤
      ∫ z, 2 * y ^ 2 * ((y ^ 2 - z ^ 2)⁻¹) ^ 2 - (y ^ 2 - z ^ 2)⁻¹ ∂μ at hle
  rw [integral_const_mul] at hle
  simpa only [singularValueEdgeMoment, div_eq_mul_inv, one_mul, mul_comm] using hle

/-- Edge thickness controls the actual negative logarithmic derivative. -/
theorem sqrt_edgeMoment_div_two_le_neg_deriv_div_singularValuePhi
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {b y : ℝ}
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    Real.sqrt (singularValueEdgeMoment μ y) / 2 ≤
      -deriv (singularValuePhi μ) y / singularValuePhi μ y := by
  have hk := memLp_two_inv_sub_of_support_subset_Icc μ hsupport hy
  have hv := variance_nonneg (fun z => (y - z)⁻¹) μ
  rw [variance_eq_sub hk] at hv
  have hN : 0 ≤ singularValueEdgeMoment μ y := integral_nonneg fun z => sq_nonneg _
  have hs := Real.sq_sqrt hN
  have hroot := Real.sqrt_nonneg (singularValueEdgeMoment μ y)
  have hM : (∫ z, (y - z)⁻¹ ∂μ) ≤ Real.sqrt (singularValueEdgeMoment μ y) := by
    change 0 ≤ singularValueEdgeMoment μ y - (∫ z, (y - z)⁻¹ ∂μ) ^ 2 at hv
    nlinarith
  have hφ := (singularValuePhi_le_integral_inv_sub μ hb hsupport hy).trans hM
  have hm := mul_le_mul_of_nonneg_left hφ hroot
  have hd := div_two_edgeMoment_le_neg_deriv_singularValuePhi μ hb hsupport hy
  apply (le_div_iff₀ (singularValuePhi_pos μ hb hsupport hy)).mpr
  nlinarith

/-- The actual root function has an explicit negative edge-thickness bound. -/
theorem singularValuePsi_le_neg_sqrt_edgeMoment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {γ b y : ℝ}
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 < b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValuePsi μ γ y ≤ -(b / 2) * Real.sqrt (singularValueEdgeMoment μ y) - 1 := by
  let ν := dTransformCompanionMeasure μ γ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_dTransformCompanionMeasure μ hγ hγ1
  have hc := (singularValueElasticity_bounds ν hb.le
    (support_dTransformCompanionMeasure_subset μ hb.le hsupport) hy).2
  have hr := sqrt_edgeMoment_div_two_le_neg_deriv_div_singularValuePhi μ hb.le hsupport hy
  have hr' := mul_le_mul_of_nonneg_left hr (hb.trans hy).le
  have hb' := mul_le_mul_of_nonneg_right hy.le
    (div_nonneg (Real.sqrt_nonneg (singularValueEdgeMoment μ y)) (by norm_num : (0 : ℝ) ≤ 2))
  rw [singularValuePsi_eq_add_elasticity μ hγ hγ1 hb.le hsupport hy]
  change singularValueElasticity μ y + singularValueElasticity ν y ≤ _
  have he : singularValueElasticity μ y ≤ -(b / 2) * Real.sqrt (singularValueEdgeMoment μ y) := by
    calc
      singularValueElasticity μ y = -(y * (-deriv (singularValuePhi μ) y /
          singularValuePhi μ y)) := by unfold singularValueElasticity; ring
      _ ≤ -(b * (Real.sqrt (singularValueEdgeMoment μ y) / 2)) :=
        neg_le_neg (hb'.trans hr')
      _ = _ := by ring
  linarith

/-- The thickness condition forces the actual D-transform root function to
tend to negative infinity at the right support edge.
Source: ScreeNOT, Lemma 8(2), Supplement Appendix A.
atlas: scree-threshold-root (partial) -/
theorem tendsto_singularValuePsi_atBot_of_edge_thickness
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {γ b : ℝ}
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hb : 0 < b)
    (hsupport : μ.support ⊆ Icc 0 b)
    (hthick : Tendsto (singularValueEdgeMoment μ) (𝓝[>] b) atTop) :
    Tendsto (singularValuePsi μ γ) (𝓝[>] b) atBot := by
  have ht := (Real.tendsto_sqrt_atTop.comp hthick).const_mul_atTop_of_neg
    (show -(b / 2) < 0 by linarith)
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [ht.eventually_le_atBot (M + 1), self_mem_nhdsWithin] with y hM hy
  change -(b / 2) * Real.sqrt (singularValueEdgeMoment μ y) ≤ M + 1 at hM
  have hbound := singularValuePsi_le_neg_sqrt_edgeMoment μ hγ hγ1 hb hsupport hy
  linarith

end NLAlib

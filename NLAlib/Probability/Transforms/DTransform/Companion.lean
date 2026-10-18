import NLAlib.Probability.Transforms.DTransform.Basic

/-!
# The rectangular companion as an actual probability law

Mixing the original law with an atom at zero realizes the companion transform
and preserves its upper support edge. Source: ScreeNOT, Supplement Appendix A.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped Topology
namespace NLAlib

/-- The companion mixture is an actual probability measure. -/
theorem isProbabilityMeasure_dTransformCompanionMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsProbabilityMeasure (dTransformCompanionMeasure μ γ) := by
  constructor
  change ENNReal.ofReal γ * μ univ + ENNReal.ofReal (1 - γ) * (Measure.dirac (0 : ℝ)) univ = 1
  rw [measure_univ, measure_univ, mul_one, mul_one,
    ← ENNReal.ofReal_add hγ (sub_nonneg.mpr hγ1)]
  simp

/-- The rectangular companion law has the same nonnegative support bound. -/
theorem support_dTransformCompanionMeasure_subset (μ : Measure ℝ) {γ b : ℝ}
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) :
    (dTransformCompanionMeasure μ γ).support ⊆ Icc 0 b := by
  apply (dTransformCompanionMeasure μ γ).support_subset_of_isClosed isClosed_Icc
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure (μ.ae_mem_Icc_of_support_subset hsupport) _
  · exact Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl, hb⟩) _

/-- A positive mixture weight preserves the actual positive upper support
point, so strict elasticity monotonicity remains available. -/
theorem mem_support_dTransformCompanionMeasure (μ : Measure ℝ) {γ b : ℝ}
    (hγ : 0 < γ) (hbmem : b ∈ μ.support) :
    b ∈ (dTransformCompanionMeasure μ γ).support := by
  apply (Measure.mem_support_iff_forall b).mpr
  intro U hU
  have hμU := (Measure.mem_support_iff_forall b).mp hbmem U hU
  have hp : 0 < ENNReal.ofReal γ * μ U :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hγ).ne' hμU.ne'
  apply hp.trans_le
  change ENNReal.ofReal γ * μ U ≤
    ENNReal.ofReal γ * μ U + ENNReal.ofReal (1 - γ) * (Measure.dirac (0 : ℝ)) U
  exact le_add_of_nonneg_right bot_le

/-- Above the support, the actual zero-atom mixture transform is exactly the
rectangular companion transform, including the endpoint mixture weights. -/
theorem singularValuePhi_dTransformCompanionMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {γ b y : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) :
    singularValuePhi (dTransformCompanionMeasure μ γ) y = singularValueCompanionPhi μ γ y := by
  have hi : Integrable (fun z => y / (y ^ 2 - z ^ 2)) μ := by
    simpa only [zero_add, pow_one, div_eq_mul_inv] using
      (integrable_dTransformMoment_kernel μ hb hsupport hy 0).const_mul y
  have hid : Integrable (fun z : ℝ => y / (y ^ 2 - z ^ 2)) (Measure.dirac 0) :=
    integrable_dirac (by finiteness)
  unfold singularValuePhi dTransformCompanionMeasure
  rw [integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top)
      (hid.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal hγ, ENNReal.toReal_ofReal (sub_nonneg.mpr hγ1)]
  unfold singularValueCompanionPhi singularValuePhi
  simp only [smul_eq_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  congr 1
  field_simp [(lt_of_le_of_lt hb hy).ne']

end NLAlib

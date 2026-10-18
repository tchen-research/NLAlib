import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Interchanging a finite measure with a curve Cauchy kernel

For a `C¹` path disjoint from a compact support interval, the joint Cauchy
kernel with its parameter derivative is continuous on a compact rectangle.
This proves its integrability and the Fubini interchange directly. No scalar
Cauchy formula, Jordan-curve interior, or winding number is assumed or asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped unitInterval
namespace MeasureTheory

private theorem curveIntegral_smul_id_eq_integral_Icc {c d : ℂ}
    (γ : Path c d) (g : ℂ → ℂ) :
    curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ =
      ∫ t in Icc (0 : ℝ) 1, derivWithin γ.extend (Icc (0 : ℝ) 1) t * g (γ.extend t) := by
  rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  ext t
  simp only [curveIntegralFun_def, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_comm]

private theorem curveIntegrable_integrable_and_integral_curveIntegral_div_sub
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {c d : ℂ} (γ : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, γ.extend t ≠ (x : ℂ))
    {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    CurveIntegrable
      (fun z => (f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) •
        ContinuousLinearMap.id ℂ ℂ) γ ∧
    Integrable (fun x : ℝ => curveIntegral
      (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) γ) μ ∧
    (∫ x : ℝ, curveIntegral
      (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) γ ∂μ) =
      curveIntegral
        (fun z => (f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) •
          ContinuousLinearMap.id ℂ ℂ) γ := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let H : ℝ × ℝ → ℂ := fun xt =>
    derivWithin γ.extend (Icc (0 : ℝ) 1) xt.2 *
      (f (γ.extend xt.2) / (γ.extend xt.2 - (xt.1 : ℂ)))
  have hc : ContinuousOn H (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have hfcomp : ContinuousOn (fun xt : ℝ × ℝ => f (γ.extend xt.2))
        (Icc a b ×ˢ Icc (0 : ℝ) 1) := hf.comp
          (show ContinuousOn (fun xt : ℝ × ℝ => γ.extend xt.2) _ by fun_prop)
          (fun xt hxt => ⟨⟨xt.2, hxt.2⟩, (γ.extend_apply hxt.2).symm⟩)
    apply ((hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).comp
      continuous_snd.continuousOn (fun _ hxt => hxt.2)).mul
    apply hfcomp.div (show ContinuousOn
      (fun xt : ℝ × ℝ => γ.extend xt.2 - (xt.1 : ℂ)) _ by fun_prop)
    intro xt hxt
    exact sub_ne_zero.mpr (hoff xt.2 hxt.2 xt.1 hxt.1)
  have hmem : ∀ᵐ xt ∂μ.prod ν, xt ∈ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [hs] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨hx, ht⟩
  have hInt : Integrable H (μ.prod ν) := by
    refine (hc.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [hmem] with xt hxt hnot
    exact (hnot hxt).elim
  have hswap := integral_integral_swap (f := fun x t => H (x, t))
    (by convert! hInt using 1)
  have hcurve : CurveIntegrable
      (fun z => (f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) •
        ContinuousLinearMap.id ℂ ℂ) γ := by
    rw [CurveIntegrable, intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    apply hInt.integral_prod_right.congr
    filter_upwards with t
    dsimp only [H]
    simp only [curveIntegralFun_def, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with x
    simp only [div_eq_mul_inv]
    ring
  have houter : Integrable (fun x : ℝ => curveIntegral
      (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) γ) μ := by
    simp_rw [curveIntegral_smul_id_eq_integral_Icc]
    simpa only [H, ν] using hInt.integral_prod_left
  refine ⟨hcurve, houter, ?_⟩
  simp_rw [curveIntegral_smul_id_eq_integral_Icc]
  trans ∫ t in Icc (0 : ℝ) 1, ∫ x : ℝ,
    derivWithin γ.extend (Icc (0 : ℝ) 1) t *
      (f (γ.extend t) / (γ.extend t - (x : ℂ))) ∂μ
  · simpa only [H, ν] using hswap
  · apply integral_congr_ae
    filter_upwards with t
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [div_eq_mul_inv]

/-- On a `C¹` path separated from a finite measure's compact support interval,
integration against that measure commutes with the native curve Cauchy integral.
The joint integrability needed for Fubini is proved from compactness. -/
theorem curveIntegrable_and_integral_curveIntegral_div_sub
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {c d : ℂ} (γ : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, γ.extend t ≠ (x : ℂ))
    {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    CurveIntegrable
      (fun z => (f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) •
        ContinuousLinearMap.id ℂ ℂ) γ ∧
    (∫ x : ℝ, curveIntegral
      (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) γ ∂μ) =
      curveIntegral
        (fun z => (f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) •
          ContinuousLinearMap.id ℂ ℂ) γ := by
  have h := curveIntegrable_integrable_and_integral_curveIntegral_div_sub hs γ hγ hoff hf
  exact ⟨h.1, h.2.2⟩

/-- The scalar curve Cauchy integral itself is integrable as a function of the
finite measure's support point. This is useful when assembling the interchange
along finitely many smooth pieces. -/
theorem integrable_curveIntegral_div_sub_of_contDiffOn
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {c d : ℂ} (γ : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, γ.extend t ≠ (x : ℂ))
    {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    Integrable (fun x : ℝ => curveIntegral
      (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) γ) μ :=
  (curveIntegrable_integrable_and_integral_curveIntegral_div_sub hs γ hγ hoff hf).2.1

end MeasureTheory

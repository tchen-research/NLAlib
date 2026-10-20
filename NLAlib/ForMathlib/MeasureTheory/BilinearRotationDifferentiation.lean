import NLAlib.ForMathlib.MeasureTheory.AffineDifferentiation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-! # Genuine bilinear expectation differentiation along rotation paths -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace NLAlib
variable {Ω E F G : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A bounded continuous first factor and a bounded C¹ second factor admit
actual differentiation of their bilinear expectation along a rotation of
integrable random vectors. A genuine integrable norm bound supplies all
domination; no Gaussian identity is assumed. -/
theorem hasDerivAt_integral_bilin_rotation
    (Y Z : Ω → E) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (f : E → F) (hfc : Continuous f)
    (g : E → G) (dg : E → E →L[ℝ] G)
    (hg : ∀ x, HasFDerivAt g (dg x) x) (hdgc : Continuous dg)
    (Cf Cg Cd : ℝ) (hfb : ∀ x, ‖f x‖≤Cf)
    (hgb : ∀ x, ‖g x‖≤Cg) (hdgb : ∀ x, ‖dg x‖≤Cd)
    (B : F →L[ℝ] G →L[ℝ] ℂ) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ ω, B (f (Y ω))
        (g (Real.cos t • Y ω+Real.sin t • Z ω)) ∂μ)
      (∫ ω, B (f (Y ω))
        (dg (Real.cos θ • Y ω+Real.sin θ • Z ω)
          (-Real.sin θ • Y ω+Real.cos θ • Z ω)) ∂μ) θ := by
  have hCf : 0≤Cf := (norm_nonneg (f 0)).trans (hfb 0)
  have hCg : 0≤Cg := (norm_nonneg (g 0)).trans (hgb 0)
  have hCd : 0≤Cd := (norm_nonneg (dg 0)).trans (hdgb 0)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  let W (t : ℝ) (ω : Ω) := Real.cos t • Y ω+Real.sin t • Z ω
  let D (t : ℝ) (ω : Ω) := -Real.sin t • Y ω+Real.cos t • Z ω
  let H (t : ℝ) (ω : Ω) := B (f (Y ω)) (g (W t ω))
  let H' (t : ℝ) (ω : Ω) := B (f (Y ω)) (dg (W t ω) (D t ω))
  have hWa (t : ℝ) : AEStronglyMeasurable (W t) μ :=
    (hY.aestronglyMeasurable.const_smul _).add (hZ.aestronglyMeasurable.const_smul _)
  have hDa (t : ℝ) : AEStronglyMeasurable (D t) μ :=
    (hY.aestronglyMeasurable.const_smul _).add (hZ.aestronglyMeasurable.const_smul _)
  have hfa := hfc.comp_aestronglyMeasurable hY.aestronglyMeasurable
  have hBa := B.continuous.comp_aestronglyMeasurable hfa
  have hHa (t : ℝ) : AEStronglyMeasurable (H t) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hBa.prodMk (hgc.comp_aestronglyMeasurable (hWa t)))
  have hH'a (t : ℝ) : AEStronglyMeasurable (H' t) μ := by
    have hdga := hdgc.comp_aestronglyMeasurable (hWa t)
    have hga := isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hdga.prodMk (hDa t))
    exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hBa.prodMk hga)
  have hHi : Integrable (H θ) μ := by
    apply Integrable.of_bound (hHa θ) (‖B‖*Cf*Cg)
    exact Eventually.of_forall fun ω =>
      (B.le_opNorm₂ _ _).trans (by gcongr <;> first | exact hfb _ | exact hgb _)
  have hDb (t : ℝ) (ω : Ω) : ‖D t ω‖≤‖Y ω‖+‖Z ω‖ := by
    calc
      _ ≤ ‖-Real.sin t • Y ω‖+‖Real.cos t • Z ω‖ := norm_add_le _ _
      _ ≤ ‖Y ω‖+‖Z ω‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_neg]
        gcongr
        · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one t)
        · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one t)
  have hbound (t : ℝ) (ω : Ω) : ‖H' t ω‖≤‖B‖*Cf*Cd*(‖Y ω‖+‖Z ω‖) := by
    calc
      _ ≤ ‖B‖*‖f (Y ω)‖*‖dg (W t ω) (D t ω)‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖*Cf*(Cd*(‖Y ω‖+‖Z ω‖)) := by
        gcongr
        · exact hfb _
        · exact ((dg _).le_opNorm _).trans
            ((mul_le_mul_of_nonneg_right (hdgb _) (norm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (hDb t ω) hCd))
      _ = _ := by ring
  have hdiff (ω : Ω) (t : ℝ) : HasDerivAt (fun t => H t ω) (H' t ω) t := by
    have hW : HasDerivAt (fun t => W t ω) (D t ω) t :=
      ((Real.hasDerivAt_cos t).smul_const (Y ω)).add
        ((Real.hasDerivAt_sin t).smul_const (Z ω))
    exact (B (f (Y ω))).hasFDerivAt.comp_hasDerivAt t ((hg _).comp_hasDerivAt t hW)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := H) (F' := H') (x₀ := θ) (s := Set.univ)
    (bound := fun ω => ‖B‖*Cf*Cd*(‖Y ω‖+‖Z ω‖)) Filter.univ_mem
    (Eventually.of_forall hHa) hHi (hH'a θ)
    (Eventually.of_forall fun ω t _ => hbound t ω)
    ((hY.norm.add hZ.norm).const_mul (‖B‖*Cf*Cd))
    (Eventually.of_forall fun ω t _ => hdiff ω t)).2

end NLAlib

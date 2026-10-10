import Mathlib.Probability.Moments.SubGaussian
import NLAlib.Concentration.Matrix.Defs.ScalarLaws

/-!
# The Rademacher law

The concrete Rademacher probability measure `rademacherMeasure = ½ δ₁ + ½ δ₋₁` on `ℝ`, the
bridge `IsRademacher μ r ↔ μ.map r = rademacherMeasure`, and the fact that a Rademacher variable
is sub-Gaussian with variance proxy `1` (Hoeffding's lemma on `[-1, 1]`).

`rademacherMeasure` and its probability instance are copied verbatim (name and statement) from
`NLAlib/Estimation/HutchinsonLaws.lean`, which is layer 4; this is their layer-1 home.

Atlas: `rademacher-khintchine` (sub-Gaussian half).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NLAlib

/-- The concrete Rademacher probability measure, assigning mass one half to each of
`1` and `-1`. This is exactly the law used by `IsRademacher`.
Atlas `hutchinson-unbiased`, `hutchinson-variance`.
atlas: scalar-laws-def -/
def rademacherMeasure : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)

/-- The Rademacher measure has total mass one.
Atlas `hutchinson-variance` (concrete law). -/
instance isProbabilityMeasure_rademacherMeasure : IsProbabilityMeasure rademacherMeasure := by
  constructor
  norm_num [rademacherMeasure]
  simpa only [one_div] using ENNReal.add_halves 1

/-- `r` is Rademacher under `μ` exactly when its law is `rademacherMeasure`; this is the
definition of `IsRademacher` unfolded. Tropp 2015, §4.1. Atlas `rademacher-khintchine`. -/
theorem isRademacher_iff_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : Ω → ℝ} : IsRademacher μ r ↔ μ.map r = rademacherMeasure := Iff.rfl

/-- Almost every point of the Rademacher law lies in `[-1, 1]`.
Atlas `rademacher-khintchine` (support of the law). -/
theorem ae_mem_Icc_rademacherMeasure : ∀ᵐ x ∂rademacherMeasure, x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  have hS : MeasurableSet {a : ℝ | ¬a ∈ Set.Icc (-1 : ℝ) 1} :=
    measurableSet_Icc.compl
  simp only [rademacherMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS]
  norm_num

/-- The Rademacher law has mean zero. Atlas `rademacher-khintchine`. -/
theorem integral_id_rademacherMeasure : ∫ x, x ∂rademacherMeasure = 0 := by
  have hi : ∀ a : ℝ, Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac a) :=
    fun a => (integrable_dirac (by simp)).smul_measure (by simp)
  rw [rademacherMeasure, integral_add_measure (hi 1) (hi (-1)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  norm_num

/-- **The Rademacher law is `1`-sub-Gaussian**: `𝔼 e^{t ε} ≤ e^{t²/2}`.
Hoeffding's lemma on `[-1, 1]` (Mathlib `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`).
Vershynin 2018, Example 2.5.8(ii). Atlas `rademacher-khintchine` (sub-Gaussian half). -/
theorem hasSubgaussianMGF_id_rademacherMeasure : HasSubgaussianMGF id 1 rademacherMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := rademacherMeasure)
    (X := id) aemeasurable_id ae_mem_Icc_rademacherMeasure integral_id_rademacherMeasure
  convert h using 1
  ext
  norm_num

/-- **A Rademacher variable is `1`-sub-Gaussian**: if `μ.map r = ½ δ₁ + ½ δ₋₁` then
`𝔼 e^{t r} ≤ e^{t²/2}` for every real `t`. No measurability hypothesis is needed: the law
being a probability measure forces `r` to be a.e. measurable.
Vershynin 2018, Example 2.5.8(ii); audit G1 C5. Atlas `rademacher-khintchine`
(sub-Gaussian half).
atlas: rademacher-khintchine -/
theorem hasSubgaussianMGF_of_isRademacher {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r : Ω → ℝ} (hr : IsRademacher μ r) :
    HasSubgaussianMGF r 1 μ := by
  rw [isRademacher_iff_map_eq] at hr
  have hm : AEMeasurable r μ := by
    apply AEMeasurable.of_map_ne_zero
    rw [hr]
    exact IsProbabilityMeasure.ne_zero _
  have hb : ∀ᵐ ω ∂μ, r ω ∈ Set.Icc (-1 : ℝ) 1 := by
    apply ae_of_ae_map hm
    rw [hr]
    exact ae_mem_Icc_rademacherMeasure
  have hc : μ[r] = 0 := by
    have h := integral_map hm (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [hr, integral_id_rademacherMeasure] at h
    exact h.symm
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc
  convert h using 1
  ext
  norm_num

end NLAlib

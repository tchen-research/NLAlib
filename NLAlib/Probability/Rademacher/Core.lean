import Mathlib.Probability.Moments.SubGaussian
/-!
# The Rademacher law

The concrete Rademacher probability measure `rademacherMeasure = ½ δ₁ + ½ δ₋₁` on `ℝ`, the
bridge `IsRademacher μ r ↔ μ.map r = rademacherMeasure`, and the fact that a Rademacher variable
is sub-Gaussian with variance proxy `1` (Hoeffding's lemma on `[-1, 1]`).

The predicate `IsRademacher μ r` (`μ.map r = rademacherMeasure`), the a.e.-measurability and the
first four moments of a Rademacher variable (`memLp_two_and_moments_of_isRademacher`) are here as
well.

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

/-- `r` has the Rademacher law under `μ`: `μ.map r = rademacherMeasure = ½ δ₁ + ½ δ₋₁`.
Tropp 2015, §4.1.
atlas: rademacher-khintchine, scalar-laws-def -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : Ω → ℝ) : Prop :=
  Measure.map r μ = rademacherMeasure

/-- `r` is Rademacher under `μ` exactly when its law is `rademacherMeasure`; this is the
definition of `IsRademacher`. Tropp 2015, §4.1. Atlas `rademacher-khintchine`. -/
theorem isRademacher_iff_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : Ω → ℝ} : IsRademacher μ r ↔ μ.map r = rademacherMeasure := Iff.rfl

/-- A Rademacher law already forces a.e. measurability, since its total mass is one.
Atlas `hutchinson-variance` (law-to-measurability bridge). -/
theorem aemeasurable_of_isRademacher {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ}
    (hlaw : IsRademacher μ g) : AEMeasurable g μ := by
  apply AEMeasurable.of_map_ne_zero
  intro hz
  have h := congrArg (fun ν : Measure ℝ => ν Set.univ) hz
  rw [IsRademacher] at hlaw
  rw [hlaw] at h
  norm_num at h

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
  have hm : AEMeasurable r μ := aemeasurable_of_isRademacher hr
  rw [isRademacher_iff_map_eq] at hr
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

/-- A Rademacher variable has finite second and fourth moments, mean zero, and both
even moments equal to one. Hutchinson 1989; Avron–Toledo 2011, Lemma 6;
atlas `hutchinson-variance` (law-to-moments bridge). -/
theorem memLp_two_and_moments_of_isRademacher {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : AEMeasurable g μ) (hlaw : IsRademacher μ g) :
    MemLp g 2 μ ∧ (∫ ω, g ω ∂μ) = 0 ∧ (∫ ω, g ω ^ 2 ∂μ) = 1 ∧
      Integrable (fun ω => g ω ^ 4) μ ∧ (∫ ω, g ω ^ 4 ∂μ) = 1 := by
  rw [isRademacher_iff_map_eq, rademacherMeasure] at hlaw
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  have hpm : ∀ᵐ ω ∂μ, g ω = 1 ∨ g ω = -1 := by
    rw [← ae_map_iff hg hS, hlaw, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inl rfl)) _
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inr rfl)) _
  have hbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  have hsq : ∀ᵐ ω ∂μ, g ω ^ 2 = 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  have hfour : ∀ᵐ ω ∂μ, g ω ^ 4 = 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> norm_num [h]
  refine ⟨MemLp.of_bound hg.aestronglyMeasurable 1 hbd, ?_, ?_, ?_, ?_⟩
  · have h : ∫ x, x ∂(μ.map g) = ∫ ω, g ω ∂μ :=
      integral_map hg aestronglyMeasurable_id
    have hi1 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have hi2 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    rw [← h, hlaw, integral_add_measure hi1 hi2, integral_smul_measure,
      integral_smul_measure, integral_dirac, integral_dirac]
    simp
  · rw [integral_congr_ae hsq]
    simp
  · exact (integrable_const (1 : ℝ)).congr (hfour.mono fun _ h => h.symm)
  · rw [integral_congr_ae hfour]
    simp

end NLAlib

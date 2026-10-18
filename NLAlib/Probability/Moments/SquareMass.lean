import NLAlib.Matrix.Norms.LoewnerBounds
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Square-mass bounds for full-array copies

The square mass of a difference of two Hermitian arrays is bounded by
twice the sum of their square masses. Equality of the two full-array laws
then gives an expected bound with constant four. The copies need not be
independent. An actual product-law specialization gives independent copies.

These are helpers for Brailovskaya--van Handel, arXiv:2201.05142v3,
Section 6.4, Lemma 6.11, supporting matrix-resolvent-gaussian-universality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- Two random full arrays with the same joint Hermitian bounded array law
have integrable square-difference mass and expected square-difference mass
at most four times the original expected square mass. There is no
independence assumption: equality of the full-array laws is sufficient.
Bounded support derives all integrability, including empty dimensions.
This is the copy-transport estimate used with the aggregate resolvent bound.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_integral_specNorm_sum_sub_sq_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (γ : Measure (ι → M)) [IsProbabilityMeasure γ]
    (U V : Ω → ι → M) (hU : HasLaw U γ μ) (hV : HasLaw V γ μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hHerm : ∀ i, ∀ᵐ A ∂γ, (A i).IsHermitian)
    (hBound : ∀ i, ∀ᵐ A ∂γ, specNorm (A i) ≤ R) :
    Integrable (fun ω => specNorm (∑ i, (U ω i - V ω i) ^ 2)) μ ∧
      (∫ ω, specNorm (∑ i, (U ω i - V ω i) ^ 2) ∂μ) ≤
        4 * ∫ A, specNorm (∑ i, A i ^ 2) ∂γ := by
  classical
  let := hU.isProbabilityMeasure
  let F : (ι → M) → ℝ := fun A => specNorm (∑ i, A i ^ 2)
  have hFc : Continuous F := by
    simp only [F, specNorm_eq_norm]
    fun_prop
  have hFi : Integrable F γ := by
    refine Integrable.of_bound hFc.measurable.aestronglyMeasurable
      ((Fintype.card ι : ℝ) * R ^ 2) ?_
    filter_upwards [ae_all_iff.mpr hBound] with A hA
    rw [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _)]
    change ‖∑ i, A i ^ 2‖ ≤ _
    calc
      _ ≤ ∑ i, ‖A i ^ 2‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, R ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [pow_two]
        exact (norm_mul_le _ _).trans (by
          simpa only [pow_two] using (sq_le_sq₀ (norm_nonneg (A i)) hR).mpr (hA i))
      _ = _ := by simp
  have hUi : Integrable (fun ω => F (U ω)) μ := by
    have hi : Integrable F (μ.map U) := by rwa [hU.map_eq]
    exact hi.comp_aemeasurable hU.aemeasurable
  have hVi : Integrable (fun ω => F (V ω)) μ := by
    have hi : Integrable F (μ.map V) := by rwa [hV.map_eq]
    exact hi.comp_aemeasurable hV.aemeasurable
  have hUH : ∀ᵐ ω ∂μ, ∀ i, (U ω i).IsHermitian := by
    apply ae_of_ae_map (p := fun A : ι → M => ∀ i, (A i).IsHermitian) hU.aemeasurable
    rw [hU.map_eq]
    exact ae_all_iff.mpr hHerm
  have hVH : ∀ᵐ ω ∂μ, ∀ i, (V ω i).IsHermitian := by
    apply ae_of_ae_map (p := fun A : ι → M => ∀ i, (A i).IsHermitian) hV.aemeasurable
    rw [hV.map_eq]
    exact ae_all_iff.mpr hHerm
  have hdom : ∀ᵐ ω ∂μ, specNorm (∑ i, (U ω i - V ω i) ^ 2) ≤
      2 * (F (U ω) + F (V ω)) := by
    filter_upwards [hUH, hVH] with ω hωU hωV
    exact specNorm_sum_sub_sq_le (U ω) (V ω) hωU hωV
  have hDiffMeas : AEStronglyMeasurable
      (fun ω => specNorm (∑ i, (U ω i - V ω i) ^ 2)) μ := by
    exact (hFc.measurable.comp_aemeasurable
      (hU.aemeasurable.sub hV.aemeasurable)).aestronglyMeasurable
  have hDomInt := (hUi.add hVi).const_mul 2
  have hDiffInt : Integrable (fun ω => specNorm (∑ i, (U ω i - V ω i) ^ 2)) μ := by
    refine hDomInt.mono' hDiffMeas ?_
    filter_upwards [hdom] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _), Pi.add_apply] using hω
  refine ⟨hDiffInt, ?_⟩
  have heU : (∫ ω, F (U ω) ∂μ) = ∫ A, F A ∂γ :=
    hU.integral_comp hFi.aestronglyMeasurable
  have heV : (∫ ω, F (V ω) ∂μ) = ∫ A, F A ∂γ :=
    hV.integral_comp hFi.aestronglyMeasurable
  calc
    _ ≤ ∫ ω, 2 * (F (U ω) + F (V ω)) ∂μ := integral_mono_ae hDiffInt hDomInt hdom
    _ = 2 * ((∫ ω, F (U ω) ∂μ) + ∫ ω, F (V ω) ∂μ) := by
      rw [integral_const_mul, integral_add hUi hVi]
    _ = _ := by rw [heU, heV]; dsimp [F]; ring

open scoped Matrix.Norms.L2Operator in
/-- Independent full-array copies on the actual product law satisfy the
fourfold square-mass estimate. Applying the preceding joint-law theorem
to any selected pair of copies gives the same conclusion. -/
theorem integrable_and_integral_specNorm_sum_copy_sub_sq_le
    (γ : Measure (ι → M)) [IsProbabilityMeasure γ] {R : ℝ} (hR : 0 ≤ R)
    (hHerm : ∀ i, ∀ᵐ A ∂γ, (A i).IsHermitian)
    (hBound : ∀ i, ∀ᵐ A ∂γ, specNorm (A i) ≤ R) :
    Integrable (fun p : (ι → M) × (ι → M) =>
      specNorm (∑ i, (p.1 i - p.2 i) ^ 2)) (γ.prod γ) ∧
      (∫ p : (ι → M) × (ι → M), specNorm (∑ i, (p.1 i - p.2 i) ^ 2) ∂γ.prod γ) ≤
        4 * ∫ A, specNorm (∑ i, A i ^ 2) ∂γ :=
  integrable_and_integral_specNorm_sum_sub_sq_le_of_hasLaw γ Prod.fst Prod.snd
    (measurePreserving_fst (μ := γ) (ν := γ)).hasLaw
    (measurePreserving_snd (μ := γ) (ν := γ)).hasLaw hR hHerm hBound

open scoped Matrix.Norms.L2Operator in
/-- Two independent copies of an actual measurable bounded Hermitian array
on its original probability space obey the fourfold expected square-mass
bound. The product sample copies the entire array, preserving all its
internal dependence; no independence among the coordinates is required.
All displayed expectations are integrable consequences of boundedness.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_integral_specNorm_sum_sub_sq_prod_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ι → Ω → M) (hMeas : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R) (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Z i ω).IsHermitian)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R) :
    Integrable (fun p : Ω × Ω => specNorm (∑ i, (Z i p.1 - Z i p.2) ^ 2))
      (μ.prod μ) ∧
      (∫ p : Ω × Ω, specNorm (∑ i, (Z i p.1 - Z i p.2) ^ 2) ∂μ.prod μ) ≤
        4 * ∫ ω, specNorm (∑ i, Z i ω ^ 2) ∂μ := by
  let F : Ω → ι → M := fun ω i => Z i ω
  have hFm : Measurable F := measurable_pi_iff.mpr hMeas
  let γ : Measure (ι → M) := μ.map F
  let : IsProbabilityMeasure γ := μ.isProbabilityMeasure_map hFm.aemeasurable
  have hF : HasLaw F γ μ := ⟨hFm.aemeasurable, rfl⟩
  have hγHerm : ∀ i, ∀ᵐ A ∂γ, (A i).IsHermitian := by
    intro i
    apply (ae_map_iff hFm.aemeasurable ?_).mpr
    · exact hHerm i
    · change MeasurableSet {A : ι → M | (A i)ᴴ = A i}
      exact (isClosed_eq (by fun_prop : Continuous (fun A : ι → M => (A i)ᴴ))
        (continuous_apply i)).measurableSet
  have hγBound : ∀ i, ∀ᵐ A ∂γ, specNorm (A i) ≤ R := by
    intro i
    apply (ae_map_iff hFm.aemeasurable ?_).mpr
    · exact hBound i
    · have hc : Continuous (fun A : ι → M => specNorm (A i)) := by
        simpa only [specNorm_eq_norm] using (continuous_apply i).norm
      exact (isClosed_le hc continuous_const).measurableSet
  have hU : HasLaw (fun p : Ω × Ω => F p.1) γ (μ.prod μ) :=
    hF.fun_comp (measurePreserving_fst (μ := μ) (ν := μ)).hasLaw
  have hV : HasLaw (fun p : Ω × Ω => F p.2) γ (μ.prod μ) :=
    hF.fun_comp (measurePreserving_snd (μ := μ) (ν := μ)).hasLaw
  have h := integrable_and_integral_specNorm_sum_sub_sq_le_of_hasLaw γ
    (fun p : Ω × Ω => F p.1) (fun p : Ω × Ω => F p.2) hU hV hR hγHerm hγBound
  have hc : Continuous (fun A : ι → M => specNorm (∑ i, A i ^ 2)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  have he : (∫ ω, specNorm (∑ i, Z i ω ^ 2) ∂μ) =
      ∫ A, specNorm (∑ i, A i ^ 2) ∂γ := hF.integral_comp hc.measurable.aestronglyMeasurable
  rwa [← he] at h

end NLAlib

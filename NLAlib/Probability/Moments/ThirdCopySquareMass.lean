import NLAlib.Probability.Exchangeable.ThirdCopyArrays
import NLAlib.Probability.Moments.SquareMass
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Aggregate square-mass moments of full resampling copies
Actual complete-array laws transport every pair of copy slots and every
higher moment of the complete original array square mass.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {ι E Z : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSpace E] [MeasurableSpace Z]
local notation "C" => (ι × Fin 3) → E
variable {n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- Any two full slots of the actual resampling triple have expected
aggregate transformed square-difference norm at most four times the
original expected transformed square mass. All three pairs `01`, `12`,
and `02` are instances; even coincident slots are allowed. Complete-array
law equality, not merely coordinatewise law equality, gives the bound.
The displayed support bound derives all integrability.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_integral_specNorm_sum_resamplingTriple_prod_copy_sub_sq_le
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure Z) [IsProbabilityMeasure γ]
    (L : E →L[ℝ] M) {R : ℝ} (hR : 0 ≤ R)
    (hHerm : ∀ i, ∀ᵐ x ∂ν i, (L x).IsHermitian)
    (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (a b : Fin 3) :
    Integrable (fun q : (ι × C) × Z =>
      specNorm (∑ i, (L (q.1.2 (i, a) - q.1.2 (i, b))) ^ 2))
        ((resamplingTripleMeasure ν).prod γ) ∧
      (∫ q : (ι × C) × Z,
        specNorm (∑ i, (L (q.1.2 (i, a) - q.1.2 (i, b))) ^ 2)
          ∂(resamplingTripleMeasure ν).prod γ) ≤
        4 * ∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν := by
  let G : (ι → E) → ι → M := fun x i => L (x i)
  have hGm : Measurable G := measurable_pi_iff.mpr fun i =>
    L.continuous.measurable.comp (measurable_pi_apply i)
  let δ : Measure (ι → M) := (Measure.pi ν).map G
  let : IsProbabilityMeasure δ := (Measure.pi ν).isProbabilityMeasure_map hGm.aemeasurable
  have hG : HasLaw G δ (Measure.pi ν) := ⟨hGm.aemeasurable, rfl⟩
  have hδHerm : ∀ i, ∀ᵐ A ∂δ, (A i).IsHermitian := by
    intro i
    apply (ae_map_iff hGm.aemeasurable ?_).mpr
    · have hi := (measurePreserving_eval ν i).hasLaw
      exact ae_of_ae_map (p := fun x : E => (L x).IsHermitian) hi.aemeasurable
        (by rw [hi.map_eq]; exact hHerm i)
    · change MeasurableSet {A : ι → M | (A i)ᴴ = A i}
      exact (isClosed_eq (by fun_prop : Continuous (fun A : ι → M => (A i)ᴴ))
        (continuous_apply i)).measurableSet
  have hδBound : ∀ i, ∀ᵐ A ∂δ, specNorm (A i) ≤ R := by
    intro i
    apply (ae_map_iff hGm.aemeasurable ?_).mpr
    · have hi := (measurePreserving_eval ν i).hasLaw
      exact ae_of_ae_map (p := fun x : E => specNorm (L x) ≤ R) hi.aemeasurable
        (by rw [hi.map_eq]; exact hBound i)
    · have hc : Continuous (fun A : ι → M => specNorm (A i)) := by
        simpa only [specNorm_eq_norm] using (continuous_apply i).norm
      exact (isClosed_le hc continuous_const).measurableSet
  have hU : HasLaw (fun q : (ι × C) × Z => fun i => L (q.1.2 (i, a))) δ
      ((resamplingTripleMeasure ν).prod γ) :=
    hG.comp (hasLaw_resamplingTriple_prod_full_copy ν γ a)
  have hV : HasLaw (fun q : (ι × C) × Z => fun i => L (q.1.2 (i, b))) δ
      ((resamplingTripleMeasure ν).prod γ) :=
    hG.comp (hasLaw_resamplingTriple_prod_full_copy ν γ b)
  have h := integrable_and_integral_specNorm_sum_sub_sq_le_of_hasLaw δ
    (fun q : (ι × C) × Z => fun i => L (q.1.2 (i, a)))
    (fun q : (ι × C) × Z => fun i => L (q.1.2 (i, b))) hU hV hR hδHerm hδBound
  have hc : Continuous (fun A : ι → M => specNorm (∑ i, A i ^ 2)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  have he : (∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν) =
      ∫ A, specNorm (∑ i, A i ^ 2) ∂δ := hG.integral_comp hc.measurable.aestronglyMeasurable
  rw [← he] at h
  simpa only [map_sub] using h

private theorem memLp_and_lpNorm_comp_of_hasLaw
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {ν : Measure α} {T : Ω → α} (hT : HasLaw T ν μ)
    {f : α → ℝ} {q : ℝ≥0∞} (hf : MemLp f q ν) :
    MemLp (f ∘ T) q μ ∧ lpNorm (f ∘ T) q μ = lpNorm f q ν := by
  have hMap : MemLp f q (μ.map T) := by rwa [hT.map_eq]
  have hComp : MemLp (f ∘ T) q μ := hMap.comp_of_map hT.aemeasurable
  refine ⟨hComp, ?_⟩
  rw [← toReal_eLpNorm hComp.1, ← toReal_eLpNorm hf.1]
  apply congrArg ENNReal.toReal
  have h := eLpNorm_map_measure (p := q) hMap.1 hT.aemeasurable
  rw [hT.map_eq] at h
  exact h.symm

private theorem memLp_and_lpNorm_two_mul_add_add_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {q : ℝ≥0∞}
    {f g h : Ω → ℝ} (hf : MemLp f q μ) (hg : MemLp g q μ) (hh : MemLp h q μ)
    (hq : 1 ≤ q) :
    MemLp (fun x => 2 * (f x + g x + h x)) q μ ∧
      lpNorm (fun x => 2 * (f x + g x + h x)) q μ ≤
        2 * (lpNorm f q μ + lpNorm g q μ + lpNorm h q μ) := by
  refine ⟨((hf.add hg).add hh).const_mul 2, ?_⟩
  change lpNorm (fun x => (2 : ℝ) * (f + g + h) x) q μ ≤ _
  have hscale : lpNorm (fun x => (2 : ℝ) * (f + g + h) x) q μ =
      2 * lpNorm (f + g + h) q μ := by
    simpa only [Nat.cast_ofNat] using lpNorm_fun_natCast_mul 2 (f + g + h) q μ
  rw [hscale]
  have hfg := lpNorm_add_le (g := g) hf hq
  have hfgh := lpNorm_add_le (g := h) (hf.add hg) hq
  exact mul_le_mul_of_nonneg_left (hfgh.trans (add_le_add hfg le_rfl)) (by norm_num)

omit [BorelSpace E] in
open scoped Matrix.Norms.L2Operator in
/-- The sum of the three full-copy square masses, multiplied by two, has
`Lq` norm at most six times the original entire-array square-mass norm.
The input is only the original square-mass moment. Equality of complete
array laws supplies the copy moments, so no independence from a later
resolvent observable is assumed. Empty matrix dimensions are allowed.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
This is a prerequisite for the `independent-sum-spectrum-universality` card. -/
theorem memLp_and_lpNorm_two_mul_sum_resamplingTriple_prod_copy_sq_le
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure Z) [IsProbabilityMeasure γ]
    (L : E →L[ℝ] M) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hMass : MemLp (fun x : ι → E => specNorm (∑ i, (L (x i)) ^ 2))
      q (Measure.pi ν)) :
    MemLp (fun x : (ι × C) × Z =>
      2 * (specNorm (∑ i, (L (x.1.2 (i, 0))) ^ 2) +
        specNorm (∑ i, (L (x.1.2 (i, 1))) ^ 2) +
        specNorm (∑ i, (L (x.1.2 (i, 2))) ^ 2)))
      q ((resamplingTripleMeasure ν).prod γ) ∧
      lpNorm (fun x : (ι × C) × Z =>
        2 * (specNorm (∑ i, (L (x.1.2 (i, 0))) ^ 2) +
          specNorm (∑ i, (L (x.1.2 (i, 1))) ^ 2) +
          specNorm (∑ i, (L (x.1.2 (i, 2))) ^ 2)))
        q ((resamplingTripleMeasure ν).prod γ) ≤
      6 * lpNorm (fun x : ι → E => specNorm (∑ i, (L (x i)) ^ 2))
        q (Measure.pi ν) := by
  let μ := (resamplingTripleMeasure ν).prod γ
  let F : (ι → E) → ℝ := fun x => specNorm (∑ i, (L (x i)) ^ 2)
  let T : Fin 3 → ((ι × C) × Z) → (ι → E) :=
    fun a x i => x.1.2 (i, a)
  let m : Fin 3 → ((ι × C) × Z) → ℝ := fun a x => F (T a x)
  have hm : ∀ a : Fin 3, MemLp (m a) q μ ∧
      lpNorm (m a) q μ = lpNorm F q (Measure.pi ν) := by
    intro a
    have hLaw : HasLaw (T a) (Measure.pi ν) μ :=
      hasLaw_resamplingTriple_prod_full_copy ν γ a
    exact memLp_and_lpNorm_comp_of_hasLaw hLaw hMass
  obtain ⟨hMem, hNorm⟩ := memLp_and_lpNorm_two_mul_add_add_le
    (hm 0).1 (hm 1).1 (hm 2).1 hq
  refine ⟨hMem, ?_⟩
  calc
    _ ≤ 2 * (lpNorm (m 0) q μ + lpNorm (m 1) q μ + lpNorm (m 2) q μ) := hNorm
    _ = _ := by rw [(hm 0).2, (hm 1).2, (hm 2).2]; ring

end NLAlib

import NLAlib.Matrix.Functions.ResolventCancellation
import NLAlib.Matrix.Functions.ResolventMeasurability
import NLAlib.Probability.Moments.ThirdCopySquareMass
import NLAlib.ForMathlib.MeasureTheory.FiniteUniformIntegral

/-! # Actual expected aggregate cubic resolvent remainders

The uniform selected index is canceled inside the operator-valued integral
before the norm is taken. The actual six-word aggregate estimate and joint
full-array copy laws then give explicit constants 96 and 288.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Section 6.4,
the operator-valued remainder estimate in the proof of Lemma 6.11.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
private theorem aemeasurable_resolventCubicRemainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A D F : Ω → M) (hA : AEMeasurable A μ) (hD : AEMeasurable D μ)
    (hF : AEMeasurable F μ) (a : ℝ) (ζ : ℂ) :
    AEMeasurable (fun ω => resolventCubicRemainder (A ω) (D ω) (F ω) a ζ) μ := by
  have h₀ := (measurable_matrix_resolvent ζ).comp_aemeasurable hA
  have h₁ := (measurable_matrix_resolvent ζ).comp_aemeasurable (hA.sub (hD.const_smul a))
  have h₂ := (measurable_matrix_resolvent ζ).comp_aemeasurable (hA.sub (hF.const_smul a))
  have hE := hF.sub hD
  unfold resolventCubicRemainder
  exact ((((((h₀.mul hF).mul h₂).mul hD).mul h₁).mul hD).mul h₀).add
    ((((((h₂.mul hD).mul h₁).mul hE).mul h₂).mul hD).mul h₀) |>.add
    ((((((h₂.mul hD).mul h₂).mul hD).mul h₀).mul hF).mul h₂) |>.add
    ((((((h₁.mul hE).mul h₂).mul hD).mul h₀).mul hD).mul h₁) |>.add
    ((((((h₂.mul hD).mul h₀).mul hF).mul h₂).mul hD).mul h₁) |>.add
    ((((((h₂.mul hD).mul h₂).mul hD).mul h₁).mul hE).mul h₂)

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_resolventCubicRemainder_le_uniform
    (A D F : M) (a r : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (hF : F.IsHermitian)
    (hr : 0 ≤ r) (hDn : specNorm D ≤ r) (hFn : specNorm F ≤ r)
    (hEn : specNorm (F - D) ≤ r) (hζ : ζ.im ≠ 0) :
    specNorm (resolventCubicRemainder A D F a ζ) ≤
      12 * r ^ 3 * |ζ.im|⁻¹ ^ 4 + 9 * a ^ 2 * r ^ 5 * |ζ.im|⁻¹ ^ 6 := by
  have hsq (X : M) (hX : X.IsHermitian) (hXn : specNorm X ≤ r) :
      specNorm (X ^ 2) ≤ r ^ 2 := by
    have hs : specNorm X ^ 2 = specNorm (X ^ 2) := by
      simpa only [hX.eq, pow_two] using specNorm_sq_eq_specNorm_conjTranspose_mul_self X
    rw [← hs]
    exact (sq_le_sq₀ (specNorm_nonneg _) hr).mpr hXn
  have h := specNorm_sum_resolventCubicRemainder_le A (fun _ : Unit => D)
    (fun _ : Unit => F) a r ζ hA (fun _ => hD) (fun _ => hF) hr
    (fun _ => hDn) (fun _ => hFn) (fun _ => hEn) hζ
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have hD₂ := hsq D hD hDn
  have hF₂ := hsq F hF hFn
  have hE₂ := hsq (F - D) (hF.sub hD) hEn
  have h₁ : 8 * specNorm (D ^ 2) + 2 * specNorm ((F - D) ^ 2) +
      2 * specNorm (F ^ 2) ≤ 8 * r ^ 2 + 2 * r ^ 2 + 2 * r ^ 2 := by
    linarith only [hD₂, hF₂, hE₂]
  have h₂ : 3 * specNorm (D ^ 2) + 6 * specNorm (F ^ 2) ≤ 3 * r ^ 2 + 6 * r ^ 2 := by
    linarith only [hD₂, hF₂]
  calc
    _ ≤ r * |ζ.im|⁻¹ ^ 4 *
        (8 * specNorm (D ^ 2) + 2 * specNorm ((F - D) ^ 2) + 2 * specNorm (F ^ 2)) +
        a ^ 2 * r ^ 3 * |ζ.im|⁻¹ ^ 6 * (3 * specNorm (D ^ 2) + 6 * specNorm (F ^ 2)) := h
    _ ≤ r * |ζ.im|⁻¹ ^ 4 * (8 * r ^ 2 + 2 * r ^ 2 + 2 * r ^ 2) +
        a ^ 2 * r ^ 3 * |ζ.im|⁻¹ ^ 6 * (3 * r ^ 2 + 6 * r ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
        (mul_le_mul_of_nonneg_left h₂ (by positivity))
    _ = _ := by ring

variable {ι E Z : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Z]
local notation "C" => (ι × Fin 3) → E

open scoped Matrix.Norms.L2Operator in
/-- The actual selected-index cubic resolvent remainder is integrable and
its cardinality-scaled expected operator has norm at most the original
expected square mass times the explicit coefficient with constants 96 and 288.
The measurable Hermitian base may be unbounded and may depend on all copy
and noise coordinates, but it is common to every selected index. No norm
or integrability conclusion is assumed.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_specNorm_card_smul_integral_resolventCubicRemainder_le
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure Z) [IsProbabilityMeasure γ] (L : E →L[ℝ] M)
    (A : C × Z → M)
    (hAm : AEMeasurable A ((Measure.pi fun k : ι × Fin 3 => ν k.1).prod γ))
    (hAH : ∀ᵐ q ∂(Measure.pi fun k : ι × Fin 3 => ν k.1).prod γ, (A q).IsHermitian)
    {R : ℝ} (hR : 0 ≤ R)
    (hHerm : ∀ i, ∀ᵐ x ∂ν i, (L x).IsHermitian)
    (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (a : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    let P := (Measure.pi fun k : ι × Fin 3 => ν k.1).prod γ
    let Q := (resamplingTripleMeasure ν).prod γ
    let D := fun (q : C × Z) i => L (q.1 (i, 0) - q.1 (i, 1))
    let F := fun (q : C × Z) i => L (q.1 (i, 0) - q.1 (i, 2))
    let T := fun (q : C × Z) i => resolventCubicRemainder (A q) (D q i) (F q i) a ζ
    Integrable (fun q : (ι × C) × Z => T (q.1.2, q.2) q.1.1) Q ∧
      (∀ i, Integrable (fun q : C × Z => T q i) P) ∧
      specNorm ((Fintype.card ι : ℝ) •
        (∫ q : (ι × C) × Z, T (q.1.2, q.2) q.1.1 ∂Q)) ≤
        (96 * R * |ζ.im|⁻¹ ^ 4 + 288 * a ^ 2 * R ^ 3 * |ζ.im|⁻¹ ^ 6) *
          ∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν := by
  classical
  dsimp only
  let P₀ := Measure.pi fun k : ι × Fin 3 => ν k.1
  let P := P₀.prod γ
  let Q := (resamplingTripleMeasure ν).prod γ
  let drop : (ι × C) × Z → C × Z := fun q => (q.1.2, q.2)
  let D : (C × Z) → ι → M := fun q i => L (q.1 (i, 0) - q.1 (i, 1))
  let F : (C × Z) → ι → M := fun q i => L (q.1 (i, 0) - q.1 (i, 2))
  let T : (C × Z) → ι → M := fun q i => resolventCubicRemainder (A q) (D q i) (F q i) a ζ
  let m : Fin 3 → Fin 3 → (C × Z) → ℝ := fun s t q =>
    specNorm (∑ i, (L (q.1 (i, s) - q.1 (i, t))) ^ 2)
  let σ : ℝ := ∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν
  let r : ℝ := 2 * R
  let c : ℝ := |ζ.im|⁻¹
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hc : 0 ≤ c := inv_nonneg.mpr (abs_nonneg _)
  have hdrop : MeasurePreserving drop Q P := by
    exact (measurePreserving_snd (μ := (PMF.uniformOfFintype ι).toMeasure) (ν := P)).comp
      (measurePreserving_prodAssoc (PMF.uniformOfFintype ι).toMeasure P₀ γ)
  have hAll : ∀ᵐ q ∂P, ∀ i, ∀ s : Fin 3,
      (L (q.1 (i, s))).IsHermitian ∧ specNorm (L (q.1 (i, s))) ≤ R := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro s
    have hl := (measurePreserving_eval (fun k : ι × Fin 3 => ν k.1) (i, s)).hasLaw.comp
      (measurePreserving_fst (μ := P₀) (ν := γ)).hasLaw
    apply ae_of_ae_map (p := fun x : E => (L x).IsHermitian ∧ specNorm (L x) ≤ R) hl.aemeasurable
    rw [hl.map_eq]
    filter_upwards [hHerm i, hBound i] with x hH hB
    exact ⟨hH, hB⟩
  have hE (q : C × Z) (i : ι) : F q i - D q i = L (q.1 (i, 1) - q.1 (i, 2)) := by
    simp only [F, D, map_sub]
    abel
  have hGood : ∀ᵐ q ∂P, (A q).IsHermitian ∧ ∀ i,
      (D q i).IsHermitian ∧ (F q i).IsHermitian ∧ specNorm (D q i) ≤ r ∧
        specNorm (F q i) ≤ r ∧ specNorm (F q i - D q i) ≤ r := by
    filter_upwards [hAH, hAll] with q hA hq
    refine ⟨hA, fun i => ?_⟩
    have hsub (s t : Fin 3) : specNorm (L (q.1 (i, s) - q.1 (i, t))) ≤ r := by
      rw [map_sub]
      exact (specNorm_sub_le _ _).trans (by dsimp [r]; linarith [(hq i s).2, (hq i t).2])
    refine ⟨?_, ?_, hsub 0 1, hsub 0 2, ?_⟩
    · dsimp [D]; rw [map_sub]; exact (hq i 0).1.sub (hq i 1).1
    · dsimp [F]; rw [map_sub]; exact (hq i 0).1.sub (hq i 2).1
    · rw [hE]; exact hsub 1 2
  have hLmeas (i : ι) (s : Fin 3) : Measurable (fun q : C × Z => L (q.1 (i, s))) :=
    L.continuous.measurable.comp ((measurable_pi_apply (i, s)).comp measurable_fst)
  have hDmeas (i : ι) : Measurable (fun q : C × Z => D q i) := by
    simpa only [D, map_sub] using (hLmeas i 0).fun_sub (hLmeas i 1)
  have hFmeas (i : ι) : Measurable (fun q : C × Z => F q i) := by
    simpa only [F, map_sub] using (hLmeas i 0).fun_sub (hLmeas i 2)
  have hTi (i : ι) : Integrable (fun q : C × Z => T q i) P := by
    refine Integrable.of_bound
      (aemeasurable_resolventCubicRemainder A _ _ hAm (hDmeas i).aemeasurable
        (hFmeas i).aemeasurable a ζ).aestronglyMeasurable
      (12 * r ^ 3 * c ^ 4 + 9 * a ^ 2 * r ^ 5 * c ^ 6) ?_
    filter_upwards [hGood] with q hq
    exact specNorm_resolventCubicRemainder_le_uniform (A q) (D q i) (F q i) a r ζ hq.1
      (hq.2 i).1 (hq.2 i).2.1 hr (hq.2 i).2.2.1 (hq.2 i).2.2.2.1
      (hq.2 i).2.2.2.2 hζ
  have hDs : Measurable (fun p : ι × C => L (p.2 (p.1, 0) - p.2 (p.1, 1))) := by
    apply measurable_from_prod_countable_right
    intro i
    simpa only [map_sub, Pi.sub_apply, Function.comp_def] using
      (L.continuous.measurable.comp (measurable_pi_apply (i, 0))).fun_sub
        (L.continuous.measurable.comp (measurable_pi_apply (i, 1)))
  have hFs : Measurable (fun p : ι × C => L (p.2 (p.1, 0) - p.2 (p.1, 2))) := by
    apply measurable_from_prod_countable_right
    intro i
    simpa only [map_sub, Pi.sub_apply, Function.comp_def] using
      (L.continuous.measurable.comp (measurable_pi_apply (i, 0))).fun_sub
        (L.continuous.measurable.comp (measurable_pi_apply (i, 2)))
  have hGoodSel : ∀ᵐ q ∂Q, (A (drop q)).IsHermitian ∧ ∀ i,
      (D (drop q) i).IsHermitian ∧ (F (drop q) i).IsHermitian ∧ specNorm (D (drop q) i) ≤ r ∧
        specNorm (F (drop q) i) ≤ r ∧ specNorm (F (drop q) i - D (drop q) i) ≤ r := by
    exact ae_of_ae_map (p := fun q : C × Z => (A q).IsHermitian ∧ ∀ i,
      (D q i).IsHermitian ∧ (F q i).IsHermitian ∧ specNorm (D q i) ≤ r ∧
        specNorm (F q i) ≤ r ∧ specNorm (F q i - D q i) ≤ r)
      hdrop.measurable.aemeasurable (by rw [hdrop.map_eq]; exact hGood)
  have hAmpull : AEMeasurable (A ∘ drop) Q := by
    have hh : AEMeasurable A (Q.map drop) := by rwa [hdrop.map_eq]
    exact hh.comp_aemeasurable hdrop.measurable.aemeasurable
  have hTsel : Integrable (fun q : (ι × C) × Z => T (drop q) q.1.1) Q := by
    refine Integrable.of_bound
      (aemeasurable_resolventCubicRemainder (A ∘ drop) _ _
        hAmpull (hDs.comp measurable_fst).aemeasurable
        (hFs.comp measurable_fst).aemeasurable a ζ).aestronglyMeasurable
      (12 * r ^ 3 * c ^ 4 + 9 * a ^ 2 * r ^ 5 * c ^ 6) ?_
    filter_upwards [hGoodSel] with q hq
    exact specNorm_resolventCubicRemainder_le_uniform _ _ _ a r ζ hq.1
      (hq.2 q.1.1).1 (hq.2 q.1.1).2.1 hr (hq.2 q.1.1).2.2.1
      (hq.2 q.1.1).2.2.2.1 (hq.2 q.1.1).2.2.2.2 hζ
  refine ⟨hTsel, hTi, ?_⟩
  have hm (s t : Fin 3) : Integrable (m s t) P ∧ (∫ q, m s t q ∂P) ≤ 4 * σ := by
    have hs := integrable_and_integral_specNorm_sum_resamplingTriple_prod_copy_sub_sq_le
      ν γ L hR hHerm hBound s t
    have hmc : Measurable (m s t) := by
      have hsub (i : ι) : Measurable (fun q : C × Z =>
          L (q.1 (i, s)) - L (q.1 (i, t))) := (hLmeas i s).sub (hLmeas i t)
      have hsum : Measurable (fun q : C × Z =>
          ∑ i, (L (q.1 (i, s)) - L (q.1 (i, t))) ^ 2) := by
        apply Finset.measurable_sum
        intro i _
        simpa only [pow_two] using (hsub i).matrix_mul (hsub i)
      simpa only [m, map_sub, specNorm_eq_norm, Function.comp_def] using
        continuous_norm.measurable.comp hsum
    have hi : Integrable ((m s t) ∘ drop) Q := hs.1
    have hb : (∫ q, m s t (drop q) ∂Q) ≤ 4 * σ := hs.2
    have he : (∫ q, m s t (drop q) ∂Q) = ∫ q, m s t q ∂P :=
      hdrop.hasLaw.integral_comp hmc.aestronglyMeasurable
    rw [he] at hb
    exact ⟨(hdrop.integrable_comp hmc.aestronglyMeasurable).mp hi, hb⟩
  have hAgg : Integrable (fun q : C × Z => ∑ i, T q i) P :=
    integrable_finsetSum _ (fun i _ => hTi i)
  have hAverage : (Fintype.card ι : ℝ) •
        (∫ q : (ι × C) × Z, T (drop q) q.1.1 ∂Q) =
      ∫ q : C × Z, ∑ i, T q i ∂P := by
    exact card_smul_integral_uniform_prod_prod P₀ γ (fun i x z => T (x, z) i) hTsel
  have hPoint : ∀ᵐ q ∂P, specNorm (∑ i, T q i) ≤
      r * c ^ 4 * (8 * m 0 1 q + 2 * m 1 2 q + 2 * m 0 2 q) +
        a ^ 2 * r ^ 3 * c ^ 6 * (3 * m 0 1 q + 6 * m 0 2 q) := by
    filter_upwards [hGood] with q hq
    have h := specNorm_sum_resolventCubicRemainder_le (A q) (D q) (F q) a r ζ hq.1
      (fun i => (hq.2 i).1) (fun i => (hq.2 i).2.1) hr
      (fun i => (hq.2 i).2.2.1) (fun i => (hq.2 i).2.2.2.1)
      (fun i => (hq.2 i).2.2.2.2) hζ
    simpa only [hE] using h
  have hB₀ : Integrable (fun q : C × Z => 8 * m 0 1 q + 2 * m 1 2 q) P :=
    ((hm 0 1).1.const_mul 8).add ((hm 1 2).1.const_mul 2)
  have hB₁ : Integrable (fun q : C × Z => 8 * m 0 1 q + 2 * m 1 2 q + 2 * m 0 2 q) P :=
    hB₀.add ((hm 0 2).1.const_mul 2)
  have hB₂ : Integrable (fun q : C × Z => 3 * m 0 1 q + 6 * m 0 2 q) P :=
    ((hm 0 1).1.const_mul 3).add ((hm 0 2).1.const_mul 6)
  have hBudget : Integrable (fun q : C × Z =>
      r * c ^ 4 * (8 * m 0 1 q + 2 * m 1 2 q + 2 * m 0 2 q) +
        a ^ 2 * r ^ 3 * c ^ 6 * (3 * m 0 1 q + 6 * m 0 2 q)) P :=
    (hB₁.const_mul (r * c ^ 4)).add (hB₂.const_mul (a ^ 2 * r ^ 3 * c ^ 6))
  rw [hAverage, specNorm_eq_norm]
  calc
    _ ≤ ∫ q : C × Z, specNorm (∑ i, T q i) ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ q : C × Z,
        r * c ^ 4 * (8 * m 0 1 q + 2 * m 1 2 q + 2 * m 0 2 q) +
          a ^ 2 * r ^ 3 * c ^ 6 * (3 * m 0 1 q + 6 * m 0 2 q) ∂P :=
      integral_mono_ae hAgg.norm hBudget hPoint
    _ = r * c ^ 4 *
        (8 * (∫ q, m 0 1 q ∂P) + 2 * (∫ q, m 1 2 q ∂P) + 2 * (∫ q, m 0 2 q ∂P)) +
          a ^ 2 * r ^ 3 * c ^ 6 * (3 * (∫ q, m 0 1 q ∂P) + 6 * (∫ q, m 0 2 q ∂P)) := by
      rw [integral_add (hB₁.const_mul (r * c ^ 4))
        (hB₂.const_mul (a ^ 2 * r ^ 3 * c ^ 6)), integral_const_mul, integral_const_mul]
      rw [integral_add hB₀ ((hm 0 2).1.const_mul 2),
        integral_add ((hm 0 1).1.const_mul 8) ((hm 1 2).1.const_mul 2),
        integral_add ((hm 0 1).1.const_mul 3) ((hm 0 2).1.const_mul 6)]
      simp only [integral_const_mul]
    _ ≤ r * c ^ 4 * (8 * (4 * σ) + 2 * (4 * σ) + 2 * (4 * σ)) +
          a ^ 2 * r ^ 3 * c ^ 6 * (3 * (4 * σ) + 6 * (4 * σ)) := by
      have h01 := (hm 0 1).2
      have h12 := (hm 1 2).2
      have h02 := (hm 0 2).2
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [h01, h12, h02]
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [h01, h02]
    _ = _ := by dsimp [r, c, σ]; ring

end NLAlib

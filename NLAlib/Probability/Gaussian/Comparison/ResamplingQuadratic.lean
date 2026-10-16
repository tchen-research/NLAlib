import NLAlib.ForMathlib.Probability.IndependentQuadratic
import NLAlib.Probability.Exchangeable.ThirdCopyBilinear

/-!
# Quadratic affine transport for actual independent resampling

The genuine same-index difference is independent of the second replacement.
Adjoining an independent probability sample preserves the needed joint
independence. The full coordinate quadratic contraction then replaces the
second-replacement affine test by the original-sum affine test in expectation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

private theorem indepFun_fst_pair_of_indepFun
    {Ω A C Z : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace C] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] (γ : Measure Z) [IsProbabilityMeasure γ]
    (D : Ω → A) (W : Ω → C) (hDm : Measurable D) (hWm : Measurable W)
    (hDW : IndepFun D W P) :
    IndepFun (fun q : Ω × Z => D q.1) (fun q => (W q.1, q.2)) (P.prod γ) := by
  let δ := P.map D
  let η := P.map W
  have : IsProbabilityMeasure δ := Measure.isProbabilityMeasure_map hDm.aemeasurable
  have : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hWm.aemeasurable
  have hD : MeasurePreserving D P δ := ⟨hDm, rfl⟩
  have hW : MeasurePreserving W P η := ⟨hWm, rfl⟩
  have hpair : MeasurePreserving (fun p => (D p, W p)) P (δ.prod η) :=
    ⟨hDm.prodMk hWm, hDW.map_prod_eq_prod_map_map hDm.aemeasurable hWm.aemeasurable⟩
  have hj := (measurePreserving_prodAssoc δ η γ).comp
    (hpair.prod (MeasurePreserving.id γ))
  have hDl := (hD.comp (measurePreserving_fst (μ := P) (ν := γ))).hasLaw
  have hWl := (hW.prod (MeasurePreserving.id γ)).hasLaw
  exact (indepFun_iff_hasLaw_prodMk_prod hDl hWl).mpr hj.hasLaw

variable {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Nonempty ι] [DecidableEq κ] in
private theorem measurable_resamplingTriple_first_coords :
    Measurable (resamplingTripleFirst : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) := by
  apply measurable_from_prod_countable_right
  intro i
  change Measurable (fun x : (ι × Fin 3) → κ → ℝ => ∑ j, x (j, if j = i then 1 else 0))
  fun_prop

omit [Nonempty ι] [DecidableEq κ] in
private theorem measurable_resamplingTriple_second_coords :
    Measurable (resamplingTripleSecond : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) := by
  apply measurable_from_prod_countable_right
  intro i
  change Measurable (fun x : (ι × Fin 3) → κ → ℝ => ∑ j, x (j, if j = i then 2 else 0))
  fun_prop

/-- The genuine quadratic resampling integrand is integrable for every bounded
continuous derivative field and an arbitrary independent probability sample.
Only individual summand second moments are needed.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integrable_bilin_quadratic_resamplingTriple_affine
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ]
    (μ : κ → ℝ) (a b : ℝ)
    (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F) (hdf : Continuous df)
    (C : ℝ) (hdfb : ∀ x, ‖df x‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    Integrable (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) =>
      B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
        (df (μ + a • (resamplingTripleSecond q.1 - μ) + b • q.2)
          (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)))
      ((resamplingTripleMeasure ν).prod γ) := by
  let P := resamplingTripleMeasure ν
  let D : (ι × ((ι × Fin 3) → κ → ℝ)) → κ → ℝ :=
    resamplingTripleOriginal - resamplingTripleFirst
  have hD : MemLp D 2 P :=
    (memLp_resamplingTriple_sums ν hν).1.sub (memLp_resamplingTriple_sums ν hν).2.1
  have hDQ := hD.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := γ))
  let W : ((ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ)) → (κ → ℝ) × (κ → ℝ) :=
    fun q => (resamplingTripleSecond q.1, q.2)
  have hW : Measurable W :=
    (measurable_resamplingTriple_second_coords.comp measurable_fst).prodMk measurable_snd
  exact integrable_bilin_quadratic_of_memLp _ hDQ W hW.aemeasurable
    (fun w => df (μ + a • (w.1 - μ) + b • w.2)) (by fun_prop)
    C (fun w => hdfb _) B

/-- The actual second-replacement quadratic test contracts into the actual
resampling second-moment tensor and the original-sum affine derivative test.
The extra sample law is arbitrary; no Gaussian or matching-covariance
assumption is used in this exact transport identity.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_quadratic_resamplingTriple_affine
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ]
    (μ : κ → ℝ) (a b : ℝ)
    (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F) (hdf : Continuous df)
    (C : ℝ) (hdfb : ∀ x, ‖df x‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    (∫ q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ),
      B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
        (df (μ + a • (resamplingTripleSecond q.1 - μ) + b • q.2)
          (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1))
      ∂((resamplingTripleMeasure ν).prod γ)) =
      ∑ i, ∑ j,
        (∫ p, (resamplingTripleOriginal p i - resamplingTripleFirst p i) *
          (resamplingTripleOriginal p j - resamplingTripleFirst p j) ∂resamplingTripleMeasure ν) •
        ∫ q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ),
          B (Pi.single i 1)
            (df (μ + a • (resamplingTripleOriginal q.1 - μ) + b • q.2) (Pi.single j 1))
          ∂((resamplingTripleMeasure ν).prod γ) := by
  let P := resamplingTripleMeasure ν
  let D : (ι × ((ι × Fin 3) → κ → ℝ)) → κ → ℝ :=
    resamplingTripleOriginal - resamplingTripleFirst
  have hD : MemLp D 2 P :=
    (memLp_resamplingTriple_sums ν hν).1.sub (memLp_resamplingTriple_sums ν hν).2.1
  have hDm : Measurable D := by
    apply Measurable.sub
    · unfold resamplingTripleOriginal
      fun_prop
    · exact measurable_resamplingTriple_first_coords
  have hXm : Measurable
      (resamplingTripleOriginal : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) := by
    unfold resamplingTripleOriginal
    fun_prop
  have hXpm := measurable_resamplingTriple_second_coords (ι := ι) (κ := κ)
  let W : ((ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ)) → (κ → ℝ) × (κ → ℝ) :=
    fun q => (resamplingTripleSecond q.1, q.2)
  have hWm : Measurable W := (hXpm.comp measurable_fst).prodMk measurable_snd
  have hind : IndepFun (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) => D q.1)
      W (P.prod γ) := indepFun_fst_pair_of_indepFun γ D resamplingTripleSecond hDm hXpm
        (indepFun_resamplingTriple_difference_second ν)
  have hDQ := hD.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := γ))
  have h := integral_bilin_quadratic_eq_sum_of_indepFun _ hDQ W hWm.aemeasurable hind
    (fun w => df (μ + a • (w.1 - μ) + b • w.2)) (by fun_prop)
    C (fun w => hdfb _) B
  have hid : IdentDistrib W
      (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) =>
        (resamplingTripleOriginal q.1, q.2)) (P.prod γ) (P.prod γ) := by
    have hpp : MeasurePreserving resamplingTripleSecond P (P.map resamplingTripleSecond) :=
      ⟨hXpm, rfl⟩
    have hpo : MeasurePreserving resamplingTripleOriginal P (P.map resamplingTripleOriginal) :=
      ⟨hXm, rfl⟩
    refine ⟨hWm.aemeasurable, (hXm.comp measurable_fst |>.prodMk measurable_snd).aemeasurable, ?_⟩
    change Measure.map (Prod.map resamplingTripleSecond id) (P.prod γ) =
      Measure.map (Prod.map resamplingTripleOriginal id) (P.prod γ)
    rw [(hpp.prod (MeasurePreserving.id γ)).map_eq,
      (hpo.prod (MeasurePreserving.id γ)).map_eq,
      (identDistrib_resamplingTripleSecond_original ν).map_eq]
  simp only [Function.comp_apply] at h
  change (∫ q, B (D q.1)
    (df (μ + a • ((W q).1 - μ) + b • (W q).2) (D q.1)) ∂P.prod γ) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hmom : (∫ q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ),
      D q.1 i * D q.1 j ∂P.prod γ) = ∫ p, D p i * D p j ∂P :=
    (measurePreserving_fst (μ := P) (ν := γ)).hasLaw.integral_comp
      (((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (hD.eval i) (hD.eval j)).integrable
        le_rfl).aestronglyMeasurable
  have htest := (hid.comp (show Measurable (fun w : (κ → ℝ) × (κ → ℝ) =>
      B (Pi.single i 1) (df (μ + a • (w.1 - μ) + b • w.2) (Pi.single j 1))) from
      ((B _).continuous.comp (hdf.comp (by fun_prop) |>.clm_apply continuous_const)).measurable)).integral_eq
  simp only [Function.comp_apply] at htest
  rw [hmom, htest]
  rfl

end NLAlib

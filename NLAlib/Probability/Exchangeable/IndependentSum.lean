import NLAlib.Probability.Exchangeable.Resampling
import NLAlib.ForMathlib.MeasureTheory.ProductConditional

/-!
# A Stein pair for independent, nonidentical summands

The probability space contains the independent summands, an independent uniform
index, and independent copies with the corresponding individual laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The canonical probability space for a sum, a uniform resampling index, and
an independent copy of every summand. The individual laws may differ. -/
def independentResamplingMeasure (ν : ι → Measure E) :
    Measure ((ι → E) × (ι × (ι → E))) :=
  (Measure.pi ν).prod ((PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν))

/-- The independent resampling construction is a probability measure. -/
instance isProbabilityMeasure_independentResamplingMeasure
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (independentResamplingMeasure ν) := by
  unfold independentResamplingMeasure
  infer_instance

/-- The original independent sum in the canonical resampling space. -/
def independentResamplingOriginal (p : (ι → E) × (ι × (ι → E))) : E := ∑ j, p.1 j

/-- Replace the selected original summand by the independent copy with the
same individual law. -/
def independentResamplingPartner (p : (ι → E) × (ι × (ι → E))) : E :=
  ∑ j, if j = p.2.1 then p.2.2 j else p.1 j

private def resamplingReorder (p : (ι → E) × (ι × (ι → E))) : ι × (ι → E × E) :=
  (p.2.1, fun j => (p.1 j, p.2.2 j))

private theorem measurePreserving_resamplingReorder
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (ρ : Measure ι)
    [IsProbabilityMeasure ρ] :
    MeasurePreserving resamplingReorder ((Measure.pi ν).prod (ρ.prod (Measure.pi ν)))
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j))) := by
  have h1 := (measurePreserving_prodAssoc (Measure.pi ν) ρ (Measure.pi ν)).symm
  have h2 := (Measure.measurePreserving_swap (μ := Measure.pi ν) (ν := ρ)).prod
    (MeasurePreserving.id (Measure.pi ν))
  have h3 := measurePreserving_prodAssoc ρ (Measure.pi ν) (Measure.pi ν)
  have h4 := (MeasurePreserving.id ρ).prod
    (measurePreserving_arrowProdEquivProdArrow E E ι ν ν).symm
  exact h4.comp (h3.comp (h2.comp h1))

/-- Uniform independent-coordinate replacement is an actual exchangeable pair,
even when the summand laws differ. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem identDistrib_independentResampling_pair
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IdentDistrib (fun p => (independentResamplingOriginal p, independentResamplingPartner p))
      (fun p => (independentResamplingPartner p, independentResamplingOriginal p))
      (independentResamplingMeasure ν) (independentResamplingMeasure ν) := by
  let ρ := (PMF.uniformOfFintype ι).toMeasure
  have hm := measurePreserving_resamplingReorder ν ρ
  have hi : IdentDistrib resamplingReorder id (independentResamplingMeasure ν)
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j))) :=
    ⟨hm.measurable.aemeasurable, aemeasurable_id,
      by simpa only [independentResamplingMeasure, ρ, Measure.map_id] using hm.map_eq⟩
  have hp : Measurable (fun p : ι × (ι → E × E) => (resamplingOriginal p, resamplingPartner p)) := by
    unfold resamplingOriginal resamplingPartner
    apply Measurable.prodMk
    · fun_prop
    · apply Finset.measurable_sum
      intro j hj
      apply Measurable.ite
      · convert ((measurableSet_singleton j).preimage
          (measurable_fst : Measurable (Prod.fst : ι × (ι → E × E) → ι))) using 1
        ext p; simp [eq_comm]
      · fun_prop
      · fun_prop
  have hq : Measurable (fun p : ι × (ι → E × E) => (resamplingPartner p, resamplingOriginal p)) :=
    measurable_swap.comp hp
  have h := (hi.comp hp).trans ((identDistrib_resampling_pair ν ρ).trans (hi.comp hq).symm)
  simpa only [Function.comp_def, id_eq, resamplingReorder,
    resamplingOriginal, resamplingPartner, independentResamplingOriginal,
    independentResamplingPartner] using h

/-- Exact selected-coordinate difference in the canonical resampling space. -/
theorem independentResamplingOriginal_sub_partner (p : (ι → E) × (ι × (ι → E))) :
    independentResamplingOriginal p - independentResamplingPartner p = p.1 p.2.1 - p.2.2 p.2.1 := by
  exact resamplingOriginal_sub_partner (resamplingReorder p)

private theorem integrable_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : E → E) (ν i)) (ρ : Measure ι) [IsProbabilityMeasure ρ] :
    Integrable (fun p : (ι → E) × (ι × (ι → E)) => p.1 p.2.1 - p.2.2 p.2.1)
      ((Measure.pi ν).prod (ρ.prod (Measure.pi ν))) := by
  have hi (j : ι) : Integrable (fun p : (ι → E) × (ι × (ι → E)) =>
      if j = p.2.1 then p.1 j - p.2.2 j else 0)
      ((Measure.pi ν).prod (ρ.prod (Measure.pi ν))) := by
    have hx := (integrable_eval (μ := ν) (i := j) (hν j)).comp_fst (ρ.prod (Measure.pi ν))
    have hy := ((integrable_eval (μ := ν) (i := j) (hν j)).comp_snd ρ).comp_snd (Measure.pi ν)
    have hs : MeasurableSet {p : (ι → E) × (ι × (ι → E)) | j = p.2.1} := by
      convert ((measurableSet_singleton j).preimage (measurable_fst.comp measurable_snd)) using 1
      ext p; simp [eq_comm]
    refine ((hx.sub hy).indicator hs).congr (ae_of_all _ fun p => ?_)
    by_cases hp : j = p.2.1 <;> simp [Set.indicator, hp]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using
    (integrable_finsetSum Finset.univ fun j _ => hi j)

private theorem integral_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : E → E) (ν i)) (x : ι → E) :
    (∫ p : ι × (ι → E), (x p.1 - p.2 p.1)
      ∂(PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν)) =
      (Fintype.card ι : ℝ)⁻¹ • (∑ j, x j - ∑ j, ∫ t, t ∂ν j) := by
  let ρ := (PMF.uniformOfFintype ι).toMeasure
  have hi (j : ι) : Integrable (fun p : ι × (ι → E) =>
      if j = p.1 then x j - p.2 j else 0) (ρ.prod (Measure.pi ν)) := by
    have hj := (integrable_const (x j) : Integrable (fun _ : ι × (ι → E) => x j) (ρ.prod (Measure.pi ν)))
    have hy := (integrable_eval (μ := ν) (i := j) (hν j)).comp_snd ρ
    have hs : MeasurableSet {p : ι × (ι → E) | j = p.1} := by
      convert ((measurableSet_singleton j).preimage measurable_fst) using 1
      ext p; simp [eq_comm]
    refine ((hj.sub hy).indicator hs).congr (ae_of_all _ fun p => ?_)
    by_cases hp : j = p.1 <;> simp [Set.indicator, hp]
  have hi' : Integrable (fun p : ι × (ι → E) => x p.1 - p.2 p.1) (ρ.prod (Measure.pi ν)) := by
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      (integrable_finsetSum Finset.univ fun j _ => hi j)
  have hEval (j : ι) : Integrable (fun x : ι → E => x j) (Measure.pi ν) :=
    integrable_eval (μ := ν) (i := j) (hν j)
  rw [integral_prod _ hi']
  simp_rw [integral_sub (integrable_const _) (hEval _),
    integral_const, probReal_univ, one_smul, integral_eval (μ := ν)]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.smul_sum, Finset.sum_sub_distrib]

/-- Conditioning on all original summands gives the exact uniform resampling
regression. This is a genuine conditional expectation, with no assumption that
the summands have equal laws. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem condExp_independentResampling_originals
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : E → E) (ν i)) :
    condExp (MeasurableSpace.comap Prod.fst inferInstance) (independentResamplingMeasure ν)
      (independentResamplingOriginal - independentResamplingPartner) =ᵐ[independentResamplingMeasure ν]
      fun p => (Fintype.card ι : ℝ)⁻¹ •
        (independentResamplingOriginal p - ∑ j, ∫ t, t ∂ν j) := by
  have hf := integrable_selected_difference ν hν (PMF.uniformOfFintype ι).toMeasure
  have hg : StronglyMeasurable (fun x : ι → E =>
      (Fintype.card ι : ℝ)⁻¹ • (∑ j, x j - ∑ j, ∫ t, t ∂ν j)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  have h := condExp_prod_fst_of_integral_eq hf hg (integral_selected_difference ν hν)
  have he : (independentResamplingOriginal - independentResamplingPartner :
      ((ι → E) × (ι × (ι → E))) → E) =
      (fun p => p.1 p.2.1 - p.2.2 p.2.1) := by
    funext p
    exact independentResamplingOriginal_sub_partner p
  simpa only [he, independentResamplingOriginal, independentResamplingMeasure] using h

/-- The original independent sum is square-integrable when all summands are.
The resampled sum has the same second moments by exchangeability.
atlas: exchangeable-matrix-covariance (partial) -/
theorem memLp_independentResamplingOriginal
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i)) :
    MemLp independentResamplingOriginal 2 (independentResamplingMeasure ν) := by
  have hc (j : ι) : MemLp (fun x : ι → E => x j) 2 (Measure.pi ν) := by
    simpa only [Function.comp_def, id_eq] using
      (hν j).comp_measurePreserving (measurePreserving_eval ν j)
  have hs : MemLp (fun x : ι → E => ∑ j, x j) 2 (Measure.pi ν) := by
    simpa using memLp_finsetSum Finset.univ (fun j _ => hc j)
  have hf := hs.comp_measurePreserving (measurePreserving_fst (μ := Measure.pi ν)
    (ν := (PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν)))
  change MemLp (fun p : (ι → E) × (ι × (ι → E)) => ∑ j, p.1 j) 2
    ((Measure.pi ν).prod ((PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν)))
  simpa only [Function.comp_def] using hf

/-- The mean of the canonical independent sum is the sum of its individual
means; identical distributions are unnecessary.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_independentResamplingOriginal
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : E → E) (ν i)) :
    (∫ p, independentResamplingOriginal p ∂independentResamplingMeasure ν) =
      ∑ j, ∫ t, t ∂ν j := by
  have hc (j : ι) : Integrable (fun x : ι → E => x j) (Measure.pi ν) :=
    integrable_eval (μ := ν) (i := j) (hν j)
  have hs : Integrable (fun x : ι → E => ∑ j, x j) (Measure.pi ν) := by
    simpa using integrable_finsetSum Finset.univ (fun j _ => hc j)
  change (∫ p : (ι → E) × (ι × (ι → E)), ∑ j, p.1 j
    ∂(Measure.pi ν).prod ((PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν))) = _
  rw [integral_prod _ (hs.comp_fst _)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_finsetSum _ (fun j _ => hc j)]
  simp only [integral_eval (μ := ν)]

/-- Conditioning only on the original sum gives the Stein regression with
`α = 1 / card ι`. Combined with the proved exchangeability and second moments,
this verifies every hypothesis of the covariance identities for independent
nonidentical summands. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem condExp_independentResampling_sum
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : E → E) (ν i)) :
    condExp (MeasurableSpace.comap independentResamplingOriginal inferInstance)
      (independentResamplingMeasure ν)
      (independentResamplingOriginal - independentResamplingPartner) =ᵐ[independentResamplingMeasure ν]
      fun p => (Fintype.card ι : ℝ)⁻¹ •
        (independentResamplingOriginal p - ∫ t, independentResamplingOriginal t
          ∂independentResamplingMeasure ν) := by
  have hfst : Measurable (Prod.fst : ((ι → E) × (ι × (ι → E))) → (ι → E)) := measurable_fst
  have hsum : Measurable (fun x : ι → E => ∑ j, x j) := by fun_prop
  have hcomp : @Measurable ((ι → E) × (ι × (ι → E))) E
      (MeasurableSpace.comap Prod.fst inferInstance) _ independentResamplingOriginal :=
    hsum.comp (measurable_iff_comap_le.mpr le_rfl)
  have hle := hcomp.comap_le
  have hm : Measurable independentResamplingOriginal := hsum.comp hfst
  have hreg := condExp_independentResampling_originals ν hν
  rw [← integral_independentResamplingOriginal ν hν] at hreg
  have ht := condExp_condExp_of_le (μ := independentResamplingMeasure ν)
    (f := independentResamplingOriginal - independentResamplingPartner) hle hfst.comap_le
  have hg := condExp_congr_ae (m := MeasurableSpace.comap independentResamplingOriginal inferInstance) hreg
  have hXsm : StronglyMeasurable[MeasurableSpace.comap independentResamplingOriginal inferInstance]
      (independentResamplingOriginal : ((ι → E) × (ι × (ι → E))) → E) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hsm : StronglyMeasurable[MeasurableSpace.comap independentResamplingOriginal inferInstance]
      (fun p : (ι → E) × (ι × (ι → E)) => (Fintype.card ι : ℝ)⁻¹ •
        (independentResamplingOriginal p - ∫ t, independentResamplingOriginal t
          ∂independentResamplingMeasure ν)) :=
    (hXsm.sub stronglyMeasurable_const).const_smul _
  have hXi : Integrable independentResamplingOriginal (independentResamplingMeasure ν) := by
    have hc (j : ι) : Integrable (fun x : ι → E => x j) (Measure.pi ν) :=
      integrable_eval (μ := ν) (i := j) (hν j)
    have hs : Integrable (fun x : ι → E => ∑ j, x j) (Measure.pi ν) := by
      simpa using integrable_finsetSum Finset.univ (fun j _ => hc j)
    change Integrable (fun p : (ι → E) × (ι × (ι → E)) => ∑ j, p.1 j)
      ((Measure.pi ν).prod ((PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi ν)))
    exact hs.comp_fst _
  have hgi : Integrable (fun p : (ι → E) × (ι × (ι → E)) => (Fintype.card ι : ℝ)⁻¹ •
      (independentResamplingOriginal p - ∫ t, independentResamplingOriginal t
        ∂independentResamplingMeasure ν)) (independentResamplingMeasure ν) :=
    (hXi.sub (integrable_const _)).smul _
  rw [condExp_of_stronglyMeasurable hm.comap_le hsm hgi] at hg
  exact ht.symm.trans hg

end NLAlib

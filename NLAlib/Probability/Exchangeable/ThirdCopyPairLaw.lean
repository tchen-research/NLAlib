import NLAlib.Probability.Exchangeable.ThirdCopyLaws

/-!
# The resampling triple realizes the canonical resampling pair

Discarding the third independent copy preserves exactly the canonical joint
law of the original and first-resampled sums. The result uses actual finite
product measures and permits independent nonidentical summands.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Select the original and first independent copy and put the common uniform
index in the canonical resampling-coordinate order. -/
def resamplingTripleToIndependent (p : ι × ((ι × Fin 3) → E)) :
    (ι → E) × (ι × (ι → E)) :=
  (fun j => p.2 (j, 0), p.1, fun j => p.2 (j, 1))

/-- Discarding the unused third copy gives precisely the canonical resampling
probability measure, including the independent uniform index. -/
theorem measurePreserving_resamplingTripleToIndependent
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving resamplingTripleToIndependent
      (resamplingTripleMeasure ν) (independentResamplingMeasure ν) := by
  let s : ι ⊕ ι → ι × Fin 3 := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  have hs : Function.Injective s := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (congrArg Prod.fst hab)
    · have hf := congrArg Prod.snd hab
      norm_num [s] at hf
    · have hf := congrArg Prod.snd hab
      norm_num [s] at hf
    · exact congrArg Sum.inr (congrArg Prod.fst hab)
  have hsel := (hasLaw_pi_select (fun k : ι × Fin 3 => ν k.1) s hs).measurePreserving
    (by fun_prop)
  have hpack := measurePreserving_sumPiEquivProdPi
    (fun k : ι ⊕ ι => ν (s k).1)
  have hv : MeasurePreserving
      (fun x : (ι × Fin 3) → E => ((fun j => x (j, 0)), (fun j => x (j, 1))))
      (Measure.pi fun k : ι × Fin 3 => ν k.1) ((Measure.pi ν).prod (Measure.pi ν)) := by
    exact hpack.comp hsel
  let ρ := (PMF.uniformOfFintype ι).toMeasure
  have h0 := (MeasurePreserving.id ρ).prod hv
  have h1 := (measurePreserving_prodAssoc ρ (Measure.pi ν) (Measure.pi ν)).symm
  have h2 := (Measure.measurePreserving_swap (μ := ρ) (ν := Measure.pi ν)).prod
    (MeasurePreserving.id (Measure.pi ν))
  have h3 := measurePreserving_prodAssoc (Measure.pi ν) ρ (Measure.pi ν)
  exact h3.comp (h2.comp (h1.comp h0))

private theorem measurable_independentResampling_pair :
    Measurable (fun p : (ι → E) × (ι × (ι → E)) =>
      (independentResamplingOriginal p, independentResamplingPartner p)) := by
  apply Measurable.prodMk
  · unfold independentResamplingOriginal
    fun_prop
  · unfold independentResamplingPartner
    apply Finset.measurable_sum
    intro j hj
    apply Measurable.ite
    · convert (measurableSet_singleton j).preimage
        (measurable_fst.comp measurable_snd : Measurable
          (fun p : (ι → E) × (ι × (ι → E)) => p.2.1)) using 1
      ext p
      simp [eq_comm]
    · fun_prop
    · fun_prop

/-- The actual joint law of the original and first replacement in the triple
equals that of the canonical independent-resampling pair. No moment or
identical-distribution hypothesis is needed.
Source: the same-index third-copy construction, Tropp (2026), §6.3.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hasLaw_resamplingTriple_original_first
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (fun p => (resamplingTripleOriginal p, resamplingTripleFirst p))
      ((independentResamplingMeasure ν).map
        (fun p => (independentResamplingOriginal p, independentResamplingPartner p)))
      (resamplingTripleMeasure ν) := by
  have hp : HasLaw (fun p : (ι → E) × (ι × (ι → E)) =>
      (independentResamplingOriginal p, independentResamplingPartner p))
      ((independentResamplingMeasure ν).map
        (fun p => (independentResamplingOriginal p, independentResamplingPartner p)))
      (independentResamplingMeasure ν) :=
    ⟨measurable_independentResampling_pair.aemeasurable, rfl⟩
  have h := hp.comp (measurePreserving_resamplingTripleToIndependent ν).hasLaw
  have hf : (fun p : (ι → E) × (ι × (ι → E)) =>
      (independentResamplingOriginal p, independentResamplingPartner p)) ∘
      resamplingTripleToIndependent =
      fun p => (resamplingTripleOriginal p, resamplingTripleFirst p) := by
    funext p
    apply Prod.ext
    · rfl
    · simp only [Function.comp_apply, independentResamplingPartner,
        resamplingTripleToIndependent, resamplingTripleFirst]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = p.1 <;> simp [hji]
  rw [hf] at h
  exact h

/-- The canonical resampling pair and the original/first coordinates of the
actual triple have identical joint distributions.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem identDistrib_resamplingTriple_original_first
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IdentDistrib (fun p => (resamplingTripleOriginal p, resamplingTripleFirst p))
      (fun p => (independentResamplingOriginal p, independentResamplingPartner p))
      (resamplingTripleMeasure ν) (independentResamplingMeasure ν) := by
  have h := hasLaw_resamplingTriple_original_first ν
  exact ⟨h.aemeasurable, measurable_independentResampling_pair.aemeasurable, h.map_eq⟩

end NLAlib

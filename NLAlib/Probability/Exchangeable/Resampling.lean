import NLAlib.Probability.Exchangeable.Bilinear
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Independent nonidentical summand resampling

Each coordinate contains an original sample and an independent copy from its
own law. A separate index selects the coordinate to resample. Coordinate swaps
preserve this actual finite-product measure, without identical-law assumptions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The original independent sum in the resampling probability space. -/
def resamplingOriginal (p : ι × (ι → E × E)) : E := ∑ j, (p.2 j).1

/-- The sum after replacing exactly the selected summand by its independent
copy. Each coordinate may have its own probability law. -/
def resamplingPartner (p : ι × (ι → E × E)) : E :=
  ∑ j, if j = p.1 then (p.2 j).2 else (p.2 j).1

private def coordinateSwap (i : ι) (x : ι → E × E) (j : ι) : E × E :=
  if j = i then (x j).swap else x j

private theorem coordinateSwap_measurable :
    Measurable (fun p : ι × (ι → E × E) => coordinateSwap p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  exact Measurable.ite (by
      convert ((measurableSet_singleton j).preimage
        (measurable_fst : Measurable (Prod.fst : ι × (ι → E × E) → ι))) using 1
      ext p
      simp [eq_comm])
    (measurable_swap.comp ((measurable_pi_apply j).comp measurable_snd))
    ((measurable_pi_apply j).comp measurable_snd)

private theorem measurePreserving_coordinateSwap
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    MeasurePreserving (coordinateSwap i)
      (Measure.pi fun j => (ν j).prod (ν j)) (Measure.pi fun j => (ν j).prod (ν j)) := by
  change MeasurePreserving (fun (x : ι → E × E) j => if j = i then (x j).swap else x j) _ _
  refine measurePreserving_pi (fun j => (ν j).prod (ν j)) (fun j => (ν j).prod (ν j))
    (f := fun j (z : E × E) => if j = i then z.swap else z) ?_
  intro j
  by_cases hj : j = i
  · simpa only [coordinateSwap, hj, if_true] using
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap ((ν j).prod (ν j)) ((ν j).prod (ν j)))
  · simp only [hj, if_false]
    constructor
    · exact measurable_id
    · exact Measure.map_id

private theorem resamplingOriginal_measurable : Measurable (resamplingOriginal : ι × (ι → E × E) → E) := by
  unfold resamplingOriginal
  fun_prop

private theorem resamplingPartner_measurable : Measurable (resamplingPartner : ι × (ι → E × E) → E) := by
  unfold resamplingPartner
  apply Finset.measurable_sum
  intro j hj
  exact Measurable.ite (by
      convert ((measurableSet_singleton j).preimage
        (measurable_fst : Measurable (Prod.fst : ι × (ι → E × E) → ι))) using 1
      ext p
      simp [eq_comm])
    (((measurable_pi_apply j).comp measurable_snd).snd)
    (((measurable_pi_apply j).comp measurable_snd).fst)

private theorem resampling_swap (p : ι × (ι → E × E)) :
    (resamplingOriginal (p.1, coordinateSwap p.1 p.2),
      resamplingPartner (p.1, coordinateSwap p.1 p.2)) =
    (resamplingPartner p, resamplingOriginal p) := by
  apply Prod.ext
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = p.1 <;> simp [resamplingOriginal, resamplingPartner, coordinateSwap, hji]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = p.1 <;> simp [resamplingOriginal, resamplingPartner, coordinateSwap, hji]

/-- Replacing a separately selected coordinate by an independent copy produces
an actual exchangeable pair of sums. The summand laws need not be identical;
even the index law may be nonuniform. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance` (realized pair). -/
theorem identDistrib_resampling_pair
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (ρ : Measure ι) [IsProbabilityMeasure ρ] :
    IdentDistrib (fun p : ι × (ι → E × E) => (resamplingOriginal p, resamplingPartner p))
      (fun p => (resamplingPartner p, resamplingOriginal p))
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j)))
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j))) := by
  have hm := (MeasurePreserving.id ρ).skew_product coordinateSwap_measurable
    (ae_of_all ρ fun i => (measurePreserving_coordinateSwap ν i).map_eq)
  have hi : IdentDistrib (fun p : ι × (ι → E × E) => (p.1, coordinateSwap p.1 p.2)) id
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j)))
      (ρ.prod (Measure.pi fun j => (ν j).prod (ν j))) :=
    ⟨hm.measurable.aemeasurable, aemeasurable_id, by simpa using hm.map_eq⟩
  have h := hi.comp (resamplingOriginal_measurable.prodMk resamplingPartner_measurable)
  simpa only [Function.comp_def, resampling_swap, id_eq] using h.symm

/-- The resampled pair differs by the original selected coordinate minus its
independent copy, with no ordering assumptions on the index type. -/
theorem resamplingOriginal_sub_partner (p : ι × (ι → E × E)) :
    resamplingOriginal p - resamplingPartner p = (p.2 p.1).1 - (p.2 p.1).2 := by
  unfold resamplingOriginal resamplingPartner
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro j hj hji; simp [hji]
  · simp

end NLAlib

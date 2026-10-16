import NLAlib.Probability.Exchangeable.ThirdCopyMoments

/-!
# The common actual marginal law of all three resampling differences

The common law is the uniform mixture of the individual independent-copy
difference laws. Summand laws may vary with their coordinate index.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Uniform mixture of the individual summands' independent-copy difference
laws; it is shared by all three differences of the resampling triple. -/
def resamplingDifferenceLaw (ν : ι → Measure E) : Measure E :=
  (PMF.uniformOfFintype ι).toMeasure.bind
    (fun i => ((ν i).prod (ν i)).map (fun p : E × E => p.1 - p.2))

/-- Every two distinct copy slots yield precisely the same actual mixed
difference law, with no moments or identical-distribution assumptions. -/
theorem hasLaw_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (a b : Fin 3) (hab : a ≠ b) :
    HasLaw (fun p : ι × ((ι × Fin 3) → E) => p.2 (p.1, a) - p.2 (p.1, b))
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have hm : Measurable (fun p : ι × ((ι × Fin 3) → E) => p.2 (p.1, a) - p.2 (p.1, b)) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => x (i, a) - x (i, b))
    fun_prop
  apply hasLaw_prod_of_section_laws hm
  intro i
  have hd : HasLaw (fun p : E × E => p.1 - p.2)
      (((ν i).prod (ν i)).map (fun p : E × E => p.1 - p.2)) ((ν i).prod (ν i)) :=
    ⟨by fun_prop, rfl⟩
  exact hd.comp (hasLaw_resamplingTriple_coordinate_pair ν i a b hab)

/-- D=X-X' has the uniform mixture of independent-copy difference laws. -/
theorem hasLaw_resamplingTriple_original_sub_first
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleOriginal - resamplingTripleFirst)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleOriginal - resamplingTripleFirst : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 0) - p.2 (p.1, 1)) := by funext p; exact resamplingTriple_difference p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 0 1 (by decide)

/-- E=X'-X'' has the same actual marginal difference law as D. -/
theorem hasLaw_resamplingTriple_first_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleFirst - resamplingTripleSecond)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleFirst - resamplingTripleSecond : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 1) - p.2 (p.1, 2)) := by funext p; exact resamplingTriple_first_sub_second p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 1 2 (by decide)

/-- F=X-X'' has the same actual marginal difference law as D and E. -/
theorem hasLaw_resamplingTriple_original_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleOriginal - resamplingTripleSecond)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleOriginal - resamplingTripleSecond : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 0) - p.2 (p.1, 2)) := by funext p; exact resamplingTriple_difference_second p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 0 2 (by decide)

end NLAlib

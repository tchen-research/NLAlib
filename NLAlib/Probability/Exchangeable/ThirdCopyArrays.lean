import NLAlib.Probability.Exchangeable.ThirdCopy
import NLAlib.ForMathlib.MeasureTheory.ProductSelection

/-! # Full-array laws and square mass in the resampling triple

Selecting a fixed copy slot preserves the joint product law of the entire
array, before or after adjoining the selected index and independent noise.
The expected aggregate squared difference of any two slots is therefore
bounded by four times the original aggregate square mass. Coordinatewise
marginal equality alone is not used for this transport.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Section 6.4,
the expected aggregate remainders in the proof of Lemma 6.11.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {ι E Z : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSpace E] [MeasurableSpace Z]
local notation "C" => (ι × Fin 3) → E

/-- Each complete fixed-slot array in the actual three-copy construction
has the original joint product law. The selected index and independent
noise remain present in the source probability space. -/
theorem hasLaw_resamplingTriple_prod_full_copy
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure Z) [IsProbabilityMeasure γ] (a : Fin 3) :
    HasLaw (fun q : (ι × C) × Z => fun i => q.1.2 (i, a))
      (Measure.pi ν) ((resamplingTripleMeasure ν).prod γ) := by
  have hs := hasLaw_pi_select (fun k : ι × Fin 3 => ν k.1)
    (fun i => (i, a)) (by intro i j h; exact congrArg Prod.fst h)
  have hi := (measurePreserving_snd
    (μ := (PMF.uniformOfFintype ι).toMeasure)
    (ν := Measure.pi fun k : ι × Fin 3 => ν k.1)).hasLaw
  have hn := (measurePreserving_fst (μ := resamplingTripleMeasure ν) (ν := γ)).hasLaw
  exact hs.comp (hi.comp hn)

end NLAlib

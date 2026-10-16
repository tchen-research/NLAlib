import NLAlib.Probability.Exchangeable.IndependentSum
import NLAlib.ForMathlib.MeasureTheory.ProductSelection
import NLAlib.ForMathlib.MeasureTheory.IndependentSections

/-!
# A same-index third copy independent of the resampling difference

The original, first replacement, and second replacement use three independent
copies of each summand and one common index. Conditional on the index, disjoint
coordinates give independence. The second replacement has the original sum's
law for every index, so independence survives averaging nonidentical laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Three independent copies per summand and a separate uniform index. -/
def resamplingTripleMeasure (ν : ι → Measure E) : Measure (ι × ((ι × Fin 3) → E)) :=
  (PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi fun k : ι × Fin 3 => ν k.1)

/-- The genuine three-copy resampling construction is a probability measure. -/
instance isProbabilityMeasure_resamplingTripleMeasure
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (resamplingTripleMeasure ν) := by
  unfold resamplingTripleMeasure
  infer_instance

/-- Original sum in the same-index three-copy construction. -/
def resamplingTripleOriginal (p : ι × ((ι × Fin 3) → E)) : E := ∑ j, p.2 (j, 0)

/-- Replace the selected coordinate by its first independent copy. -/
def resamplingTripleFirst (p : ι × ((ι × Fin 3) → E)) : E :=
  ∑ j, p.2 (j, if j = p.1 then 1 else 0)

/-- Replace the same selected coordinate by its second independent copy. -/
def resamplingTripleSecond (p : ι × ((ι × Fin 3) → E)) : E :=
  ∑ j, p.2 (j, if j = p.1 then 2 else 0)

private def thirdSelection (i j : ι) : ι × Fin 3 := (j, if j = i then 2 else 0)

private theorem indepFun_third_section
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    IndepFun (fun x : (ι × Fin 3) → E => x (i, 0) - x (i, 1))
      (fun x => ∑ j, x (thirdSelection i j)) (Measure.pi fun k : ι × Fin 3 => ν k.1) := by
  let S : Finset (ι × Fin 3) := {(i, 0), (i, 1)}
  let T : Finset (ι × Fin 3) := Finset.univ.image (thirdSelection i)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro k hkS hkT
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hkT
    have hji : j = i := by
      have h := hkS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact congrArg Prod.fst h
    subst j
    simpa [S, thirdSelection] using hkS
  have hi : iIndepFun (fun k (x : (ι × Fin 3) → E) => x k)
      (Measure.pi fun k : ι × Fin 3 => ν k.1) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := hi.indepFun_finset S T hST (fun _ => by fun_prop)
  let f : (S → E) → E := fun x => x ⟨(i, 0), by simp [S]⟩ - x ⟨(i, 1), by simp [S]⟩
  let g : (T → E) → E := fun x => ∑ j, x ⟨thirdSelection i j, by simp [T]⟩
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  simpa only [Function.comp_def, f, g] using hind.comp hf hg

private theorem hasLaw_third_section
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    HasLaw (fun x : (ι × Fin 3) → E => ∑ j, x (thirdSelection i j))
      ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j))
      (Measure.pi fun k : ι × Fin 3 => ν k.1) := by
  have hsel := hasLaw_pi_select (fun k : ι × Fin 3 => ν k.1) (thirdSelection i)
    (by intro j k h; exact congrArg Prod.fst h)
  have hs : HasLaw (fun x : ι → E => ∑ j, x j)
      ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j)) (Measure.pi ν) :=
    ⟨by fun_prop, rfl⟩
  exact hs.comp hsel

/-- The second replacement has the original independent sum's law. This is
true for each fixed index before averaging. Source: Tropp (2026), §6.3. -/
theorem hasLaw_resamplingTripleSecond
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw resamplingTripleSecond ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j))
      (resamplingTripleMeasure ν) := by
  have hg : Measurable (resamplingTripleSecond : ι × ((ι × Fin 3) → E) → E) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => ∑ j, x (j, if j = i then 2 else 0))
    fun_prop
  exact hasLaw_prod_of_sections hg (fun i => hasLaw_third_section ν i)

/-- The first resampling difference uses only the selected original and its
first independent copy. -/
theorem resamplingTriple_difference (p : ι × ((ι × Fin 3) → E)) :
    resamplingTripleOriginal p - resamplingTripleFirst p = p.2 (p.1, 0) - p.2 (p.1, 1) := by
  unfold resamplingTripleOriginal resamplingTripleFirst
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single p.1]
  · simp
  · intro j hj hji; simp [hji]
  · simp

/-- In the genuine same-index resampling triple, the second replacement is
independent of the difference between the original sum and first replacement.
This includes independent nonidentical summands. Source: Tropp (2026), §6.3;
supports the Cauchy-transform universality card. -/
theorem indepFun_resamplingTriple_difference_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IndepFun (resamplingTripleOriginal - resamplingTripleFirst)
      resamplingTripleSecond (resamplingTripleMeasure ν) := by
  have hf : Measurable (fun p : ι × ((ι × Fin 3) → E) => p.2 (p.1, 0) - p.2 (p.1, 1)) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => x (i, 0) - x (i, 1))
    fun_prop
  have hg : Measurable (resamplingTripleSecond : ι × ((ι × Fin 3) → E) → E) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => ∑ j, x (j, if j = i then 2 else 0))
    fun_prop
  haveI : IsProbabilityMeasure ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j)) :=
    (Measure.pi ν).isProbabilityMeasure_map (by fun_prop)
  have h := indepFun_prod_of_sections (ρ := (PMF.uniformOfFintype ι).toMeasure) hf hg (fun i => indepFun_third_section ν i)
    (fun i => hasLaw_third_section ν i)
  have he : (resamplingTripleOriginal - resamplingTripleFirst : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 0) - p.2 (p.1, 1)) := by
    funext p
    exact resamplingTriple_difference p
  simpa only [he, resamplingTripleMeasure] using h

end NLAlib

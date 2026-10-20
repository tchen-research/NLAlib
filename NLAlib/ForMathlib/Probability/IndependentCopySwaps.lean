import Mathlib.MeasureTheory.Integral.Pi

/-!
# Independent coordinate swaps of actual product copies

Each coordinate pair has its own product law. Swapping any fixed subset of
the pairs preserves the whole product, without identically distributed
coordinates. This supplies independent-copy Rademacher symmetrization.
-/

noncomputable section
set_option autoImplicit false

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)]

/-- Independently swapping any fixed subset of coordinate pairs preserves
the actual product law of two copies of each individual marginal. -/
theorem measurePreserving_pi_prod_swap_if (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun x : ∀ i, Ω i × Ω i =>
      fun i => if p i then (x i).swap else x i)
      (Measure.pi fun i => (ν i).prod (ν i))
      (Measure.pi fun i => (ν i).prod (ν i)) := by
  apply measurePreserving_pi (fun i => (ν i).prod (ν i)) (fun i => (ν i).prod (ν i))
    (f := fun i (z : Ω i × Ω i) => if p i then z.swap else z)
  intro i
  by_cases hi : p i
  · simpa only [hi, if_true] using
      (Measure.measurePreserving_swap :
        MeasurePreserving Prod.swap ((ν i).prod (ν i)) ((ν i).prod (ν i)))
  · simp only [hi, if_false]
    exact ⟨measurable_id, Measure.map_id⟩

/-- An actual measurable test of independent coordinate pairs has unchanged
expectation after swapping any fixed subset of the pairs. -/
theorem integral_pi_prod_swap_if {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ι → Prop) [DecidablePred p]
    (f : (∀ i, Ω i × Ω i) → E)
    (hf : AEStronglyMeasurable f (Measure.pi fun i => (ν i).prod (ν i))) :
    (∫ x, f (fun i => if p i then (x i).swap else x i)
      ∂Measure.pi fun i => (ν i).prod (ν i)) =
      ∫ x, f x ∂Measure.pi fun i => (ν i).prod (ν i) := by
  have hp := measurePreserving_pi_prod_swap_if ν p
  have hfm : AEStronglyMeasurable f
      ((Measure.pi fun i => (ν i).prod (ν i)).map
        (fun x : ∀ i, Ω i × Ω i => fun i => if p i then (x i).swap else x i)) := by
    rw [hp.map_eq]
    exact hf
  have h := integral_map hp.measurable.aemeasurable hfm
  rw [hp.map_eq] at h
  exact h.symm

end MeasureTheory

/-!
# A single-coordinate swap between two full product samples

This is the full-copy form of the existing coordinate-pair swap. It is useful
when orienting one replacement term before applying a common random proxy.
-/

noncomputable section
set_option autoImplicit false

namespace MeasureTheory

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  (ν : ι → Measure Ω) [∀ i, SigmaFinite (ν i)]

/-- Swapping the same coordinate of two actual independent product samples
preserves their joint law, without requiring identically distributed marginals. -/
theorem measurePreserving_prod_pi_update_swap (i : ι) :
    MeasurePreserving (fun q : (ι → Ω) × (ι → Ω) =>
      (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i)))
      ((Measure.pi ν).prod (Measure.pi ν))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  have hp := measurePreserving_arrowProdEquivProdArrow Ω Ω ι ν ν
  have hs := measurePreserving_pi_prod_swap_if ν (fun j => j = i)
  have h := hp.comp (hs.comp hp.symm)
  apply h.congr (by fun_prop)
  exact ae_of_all _ fun q => by
    apply Prod.ext <;> ext j <;> by_cases hj : j = i <;>
      simp [Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow, hj]

/-- The integral of an actual measurable test is invariant under the
single-coordinate full-copy swap. -/
theorem integral_prod_pi_update_swap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (i : ι) (f : ((ι → Ω) × (ι → Ω)) → E)
    (hf : AEStronglyMeasurable f ((Measure.pi ν).prod (Measure.pi ν))) :
    (∫ q : (ι → Ω) × (ι → Ω),
      f (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i))
        ∂((Measure.pi ν).prod (Measure.pi ν))) =
      ∫ q, f q ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  have hp := measurePreserving_prod_pi_update_swap ν i
  have hfm : AEStronglyMeasurable f
      (((Measure.pi ν).prod (Measure.pi ν)).map
        (fun q : (ι → Ω) × (ι → Ω) =>
          (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i)))) := by
    rw [hp.map_eq]
    exact hf
  have h := integral_map hp.measurable.aemeasurable hfm
  rw [hp.map_eq] at h
  exact h.symm

end MeasureTheory

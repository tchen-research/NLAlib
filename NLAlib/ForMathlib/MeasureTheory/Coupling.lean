import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Couplings with prescribed marginals

Actual measures on a product, their marginals, measurable pushforwards, and
Markov-kernel constructions. These are the primal objects used in transport
bounds, independently of any duality theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- A product-space measure has the specified first and second marginals. -/
def IsCoupling (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop :=
  π.fst = μ ∧ π.snd = ν

namespace IsCoupling

variable {π : Measure (α × β)} {μ : Measure α} {ν : Measure β}

theorem mass_eq (h : π.IsCoupling μ ν) : μ Set.univ = ν Set.univ := by
  rw [← h.1, ← h.2, fst_univ, snd_univ]

theorem measurePreserving_fst (h : π.IsCoupling μ ν) :
    MeasurePreserving Prod.fst π μ := ⟨measurable_fst, h.1⟩

theorem measurePreserving_snd (h : π.IsCoupling μ ν) :
    MeasurePreserving Prod.snd π ν := ⟨measurable_snd, h.2⟩

theorem isProbabilityMeasure (h : π.IsCoupling μ ν) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure π where
  measure_univ := by rw [← fst_univ, h.1, measure_univ]

theorem swap (h : π.IsCoupling μ ν) : (π.map Prod.swap).IsCoupling ν μ := by
  simpa [IsCoupling] using And.intro h.2 h.1

theorem map (h : π.IsCoupling μ ν) {f : α → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    (π.map (fun p => (f p.1, g p.2))).IsCoupling (μ.map f) (ν.map g) := by
  constructor
  · have hfst := fst_map_prodMk (μ := π) (X := fun p : α × β => f p.1)
      (Y := fun p : α × β => g p.2) (by fun_prop)
    rw [hfst]
    change π.map (f ∘ Prod.fst) = μ.map f
    rw [← Measure.map_map hf measurable_fst]
    exact congrArg (Measure.map f) h.1
  · have hsnd := snd_map_prodMk (μ := π) (X := fun p : α × β => f p.1)
      (Y := fun p : α × β => g p.2) (by fun_prop)
    rw [hsnd]
    change π.map (g ∘ Prod.snd) = ν.map g
    rw [← Measure.map_map hg measurable_snd]
    exact congrArg (Measure.map g) h.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_fst (h : π.IsCoupling μ ν) {f : α → E}
    (hf : AEStronglyMeasurable f μ) : ∫ p, f p.1 ∂π = ∫ x, f x ∂μ := by
  have hf' : AEStronglyMeasurable f (π.map Prod.fst) := by
    change AEStronglyMeasurable f π.fst
    rw [h.1]
    exact hf
  rw [← integral_map measurable_fst.aemeasurable hf']
  exact congrArg (fun m => ∫ x, f x ∂m) h.1

theorem integral_snd (h : π.IsCoupling μ ν) {f : β → E}
    (hf : AEStronglyMeasurable f ν) : ∫ p, f p.2 ∂π = ∫ x, f x ∂ν := by
  have hf' : AEStronglyMeasurable f (π.map Prod.snd) := by
    change AEStronglyMeasurable f π.snd
    rw [h.2]
    exact hf
  rw [← integral_map measurable_snd.aemeasurable hf']
  exact congrArg (fun m => ∫ x, f x ∂m) h.2

end IsCoupling

/-- Independent probability laws give a coupling by their actual product measure. -/
theorem isCoupling_prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : (μ.prod ν).IsCoupling μ ν :=
  ⟨fst_prod, snd_prod⟩

/-- Pushing a measure through the diagonal gives its identity coupling. -/
theorem isCoupling_map_diag (μ : Measure α) :
    (μ.map (fun x => (x, x))).IsCoupling μ μ := by
  constructor
  · rw [fst_map_prodMk (X := fun x : α => x) (Y := fun x : α => x)
      (μ := μ) measurable_id]
    exact Measure.map_id
  · rw [snd_map_prodMk (X := fun x : α => x) (Y := fun x : α => x)
      (μ := μ) measurable_id]
    exact Measure.map_id

/-- A Markov transition and its input law give a coupling with the output law. -/
theorem isCoupling_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsMarkovKernel κ] : (μ ⊗ₘ κ).IsCoupling μ (κ ∘ₘ μ) :=
  ⟨fst_compProd μ κ, snd_compProd μ κ⟩

end MeasureTheory.Measure

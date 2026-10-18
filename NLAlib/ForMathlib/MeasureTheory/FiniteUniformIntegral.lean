import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Prod

/-! # Canceling an independent finite uniform average

Multiplying an actual Bochner integral with a separate uniform finite
index by its cardinality gives the integral of the whole finite sum.
An additional independent sample is retained through product association.
-/

noncomputable section
open MeasureTheory

namespace MeasureTheory

variable {ι Ω Z F : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω] [MeasurableSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The cardinality cancels the average over an independent finite uniform
index, leaving the actual integral of the finite sum. -/
theorem card_smul_integral_uniform_prod (μ : Measure Ω) [SFinite μ]
    (f : ι → Ω → F)
    (hf : Integrable (fun p : ι × Ω => f p.1 p.2)
      ((PMF.uniformOfFintype ι).toMeasure.prod μ)) :
    (Fintype.card ι : ℝ) •
        (∫ p : ι × Ω, f p.1 p.2 ∂(PMF.uniformOfFintype ι).toMeasure.prod μ) =
      ∫ ω, ∑ i, f i ω ∂μ := by
  classical
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [integral_prod_symm _ hf, ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (Fintype.card ι : ℝ) •
      (∫ i, f i ω ∂(PMF.uniformOfFintype ι).toMeasure) = ∑ i, f i ω
    rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- An extra independent sample survives cancellation of the finite
uniform index. Product association retains its joint dependence with the
original sample inside each integrand. -/
theorem card_smul_integral_uniform_prod_prod
    (μ : Measure Ω) [SFinite μ] (γ : Measure Z) [SFinite γ]
    (f : ι → Ω → Z → F)
    (hf : Integrable (fun q : (ι × Ω) × Z => f q.1.1 q.1.2 q.2)
      (((PMF.uniformOfFintype ι).toMeasure.prod μ).prod γ)) :
    (Fintype.card ι : ℝ) •
        (∫ q : (ι × Ω) × Z, f q.1.1 q.1.2 q.2
          ∂((PMF.uniformOfFintype ι).toMeasure.prod μ).prod γ) =
      ∫ q : Ω × Z, ∑ i, f i q.1 q.2 ∂μ.prod γ := by
  let ρ := (PMF.uniformOfFintype ι).toMeasure
  let g : ι × (Ω × Z) → F := fun p => f p.1 p.2.1 p.2.2
  have hm := measurePreserving_prodAssoc ρ μ γ
  have hg : Integrable g (ρ.prod (μ.prod γ)) :=
    (hm.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mp hf
  have he : (∫ q : (ι × Ω) × Z, f q.1.1 q.1.2 q.2 ∂(ρ.prod μ).prod γ) =
      ∫ p, g p ∂ρ.prod (μ.prod γ) := hm.integral_comp' g
  rw [he]
  exact card_smul_integral_uniform_prod (μ.prod γ) (fun i p => f i p.1 p.2) hg

end MeasureTheory

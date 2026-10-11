import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

/-!
# The actual finite uniform sequence law is a product law

Equality is proved on all singleton masses. Supports the actual iid side of
operator re-derivation `sh:convex-sampling`, atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open ProbabilityTheory
open scoped Classical ENNReal
namespace NLAlib

/-- The finite uniform function law equals the product of the coordinate
uniform laws, including the empty coordinate family. Source: `sh:convex-sampling`. -/
theorem uniform_function_toMeasure_eq_pi
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (PMF.uniformOfFintype (ι → α)).toMeasure =
      Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply,
    Fintype.card_fun, Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

/-- Coordinate compositions are genuinely independent under the actual
uniform finite sequence law. Source: product uniform law, `sh:srht-ose`. -/
theorem iIndepFun_uniform_sequence_comp
    {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] (f : α → β) :
    iIndepFun (fun a (I : ι → α) => f (I a))
      (PMF.uniformOfFintype (ι → α)).toMeasure := by
  rw [uniform_function_toMeasure_eq_pi (ι := ι) (α := α)]
  exact iIndepFun_pi (μ := fun _ : ι => (PMF.uniformOfFintype α).toMeasure)
    (X := fun _ : ι => f) (fun _ => Measurable.of_discrete.aemeasurable)

/-- Each coordinate of the actual finite uniform sequence has the exact
uniform expectation. Source: finite product integration, `sh:srht-ose`. -/
theorem integral_uniform_sequence_comp_eval
    {ι α E : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : α → E) (a : ι) :
    (∫ I : ι → α, f (I a) ∂(PMF.uniformOfFintype (ι → α)).toMeasure) =
      (1 / (Fintype.card α : ℝ)) • ∑ j, f j := by
  rw [uniform_function_toMeasure_eq_pi (ι := ι) (α := α)]
  have hev := (measurePreserving_eval (fun _ : ι =>
    (PMF.uniformOfFintype α).toMeasure) a).map_eq
  have hmap := integral_map
    (μ := Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure))
    (φ := fun I : ι → α => I a) (f := f)
    (measurable_pi_apply a).aemeasurable StronglyMeasurable.of_discrete.aestronglyMeasurable
  rw [← hmap, hev, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.smul_sum, one_div]

end NLAlib

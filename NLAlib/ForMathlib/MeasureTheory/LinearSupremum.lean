import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FunProp

/-!
# Measurable suprema of bounded finite linear tests

An arbitrary parameter class yields a lower semicontinuous supremum as a
function of its finite real coefficient vector. This supplies measurability
without any countability assumption on the parameter class.
-/

noncomputable section
set_option autoImplicit false

namespace Real
variable {ι T : Type*} [Fintype ι]

/-- Uniformly bounded coefficients give a finite upper bound for every
finite real linear test over an arbitrary parameter class. -/
theorem bddAbove_range_sum_mul_of_abs_le
    (X : ι → T → ℝ) {R : ℝ} (hX : ∀ i t, |X i t| ≤ R) (r : ι → ℝ) :
    BddAbove (Set.range fun t => ∑ i, r i * X i t) := by
  refine ⟨∑ i, |r i| * R, ?_⟩
  rintro _ ⟨t, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  exact (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
    mul_le_mul_of_nonneg_left (hX i t) (abs_nonneg _)

end Real

namespace MeasureTheory
variable {ι T : Type*} [Fintype ι]

/-- The supremum of a uniformly bounded finite family of real linear
coefficient tests is measurable, even for an uncountable parameter class. -/
theorem measurable_ciSup_sum_mul_of_bounded
    (X : ι → T → ℝ) {R : ℝ} (hX : ∀ i t, |X i t| ≤ R) :
    Measurable (fun r : ι → ℝ => ⨆ t, ∑ i, r i * X i t) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_ciSup
  · exact fun r => Real.bddAbove_range_sum_mul_of_abs_le X hX r
  · intro t
    exact (by fun_prop : Continuous (fun r : ι → ℝ => ∑ i, r i * X i t)).lowerSemicontinuous

end MeasureTheory

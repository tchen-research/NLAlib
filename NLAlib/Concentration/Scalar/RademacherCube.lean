import NLAlib.Concentration.Scalar.Rademacher
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# An actual finite independent sign cube

Independent uniform Bool coordinates encode independent Rademacher signs.
The product probability measure is represented by a standard Mathlib PMF,
with the exact measure bridge. Supports the one-diagonal classical SRHT law.
Source: operator re-derivation `sh:srht`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace NLAlib

/-- A Bool coordinate encodes the two real Rademacher signs.
Source: operator re-derivation `sh:srht`. -/
def rademacherBoolSign (b : Bool) : ℝ := if b then 1 else -1

/-- Each actual finite sign has squared value one.
Source: operator re-derivation `sh:srht`. -/
@[simp] theorem rademacherBoolSign_sq (b : Bool) : rademacherBoolSign b ^ 2 = 1 := by
  cases b <;> norm_num [rademacherBoolSign]

/-- Uniform Bool sampling pushes forward to the existing Rademacher measure.
Source: operator re-derivation `sh:srht`; exact two-atom law. -/
theorem uniformBool_map_rademacherBoolSign :
    (PMF.uniformOfFintype Bool).toMeasure.map rademacherBoolSign = rademacherMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (show Measurable rademacherBoolSign from .of_discrete) hs,
    PMF.toMeasure_apply_fintype]
  simp only [Fintype.sum_bool,
    rademacherMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs]
  have hf : (false ∈ rademacherBoolSign ⁻¹' s) ↔ (-1 : ℝ) ∈ s := Iff.rfl
  have ht : (true ∈ rademacherBoolSign ⁻¹' s) ↔ (1 : ℝ) ∈ s := Iff.rfl
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases hm : (-1 : ℝ) ∈ s <;>
    simp [Set.indicator, hf, ht, h1, hm]

/-- The concrete finite PMF for one shared diagonal of independent signs.
Source: operator re-derivation `sh:srht`; the product uniform Bool law. -/
def rademacherCubePMF (ι : Type*) [Fintype ι] : PMF (ι → Bool) :=
  (Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)).toPMF

/-- The finite cube PMF's measure is literally the product of independent
uniform Bool laws. Source: operator re-derivation `sh:srht`. -/
@[simp] theorem rademacherCubePMF_toMeasure (ι : Type*) [Fintype ι] :
    (rademacherCubePMF ι).toMeasure =
      Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) := by
  unfold rademacherCubePMF
  exact Measure.toPMF_toMeasure _

/-- The encoded sign coordinates are genuinely independent under the actual
one-diagonal cube law. Source: operator re-derivation `sh:srht`. -/
theorem iIndepFun_rademacherBoolSign_cube (ι : Type*) [Fintype ι] :
    iIndepFun (fun i (ξ : ι → Bool) => rademacherBoolSign (ξ i))
      (rademacherCubePMF ι).toMeasure := by
  rw [rademacherCubePMF_toMeasure]
  exact iIndepFun_pi (fun _ => (show AEMeasurable rademacherBoolSign _ from
    Measurable.of_discrete.aemeasurable))

/-- Each sign coordinate has the existing exact Rademacher law.
Source: operator re-derivation `sh:srht`. -/
theorem isRademacher_rademacherBoolSign_cube (ι : Type*) [Fintype ι] (i : ι) :
    IsRademacher (rademacherCubePMF ι).toMeasure (fun ξ => rademacherBoolSign (ξ i)) := by
  rw [isRademacher_iff_map_eq, rademacherCubePMF_toMeasure]
  change (Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)).map
      (rademacherBoolSign ∘ (fun ξ => ξ i)) = _
  rw [← Measure.map_map (show Measurable rademacherBoolSign from .of_discrete)
    (measurable_pi_apply i), (measurePreserving_eval _ i).map_eq,
    uniformBool_map_rademacherBoolSign]

end NLAlib

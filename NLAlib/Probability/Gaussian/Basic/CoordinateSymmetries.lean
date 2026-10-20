import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact coordinate symmetries of the Gaussian product law

Selected coordinate negations and finite coordinate permutations preserve
the actual independent standard Gaussian product measure. These native
measure-preserving maps can be composed with matrix models directly.
Source: Gaussian symmetry; arXiv:2108.06312v2, Lemma 5.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {κ : Type*} [Fintype κ]

/-- Negating any selected finite collection of independent standard real
Gaussian coordinates preserves their actual product measure. -/
theorem measurePreserving_gaussianVector_coordinate_negate
    (p : κ → Prop) [DecidablePred p] :
    MeasurePreserving (fun x : κ → ℝ => fun k => if p k then -x k else x k)
      (gaussianVector κ) (gaussianVector κ) := by
  apply measurePreserving_pi (fun _ : κ => gaussianReal 0 1)
    (fun _ : κ => gaussianReal 0 1)
    (f := fun k (t : ℝ) => if p k then -t else t)
  intro k
  by_cases hk : p k
  · simp only [if_pos hk]
    exact ⟨measurable_neg,by simp [gaussianReal_map_neg]⟩
  · simp only [if_neg hk]
    exact MeasurePreserving.id (gaussianReal (0 : ℝ) 1)

/-- Reindexing by any finite permutation preserves the true independent
standard Gaussian product measure. -/
theorem measurePreserving_gaussianVector_coordinate_permute (σ : Equiv.Perm κ) :
    MeasurePreserving (fun x : κ → ℝ => fun k => x (σ k))
      (gaussianVector κ) (gaussianVector κ) := by
  convert (measurePreserving_piCongrLeft
    (fun _ : κ => gaussianReal (0 : ℝ) 1) σ.symm) using 1
  funext x k
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

end NLAlib

end

import NLAlib.Matrix.Norms.SpectralNormBounds
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of named matrix norms

Entrywise continuity gives continuity of the finite Frobenius formula and the
spectral norm. Public statements retain the named norms, independent of scoped
matrix norm instances.
-/

noncomputable section
open scoped Topology
namespace NLAlib

variable {E m n : Type*} [TopologicalSpace E] [Fintype m] [Fintype n]
  {A : E → Matrix m n ℝ} {x : E}

/-- Entrywise continuous real matrix families have continuous Frobenius norm. -/
theorem continuousAt_frobNorm_of_entrywise
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x) :
    ContinuousAt (fun y => frobNorm (A y)) x := by
  simp only [frobNorm, frobSq_eq_sum_norm_sq]
  apply Real.continuous_sqrt.continuousAt.comp
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (hA i j).norm.pow 2

/-- Entrywise continuity gives continuity of the Frobenius distance to the
matrix at the base point. -/
theorem continuousAt_frobNorm_sub_of_entrywise
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x) :
    ContinuousAt (fun y => frobNorm (A y - A x)) x :=
  continuousAt_frobNorm_of_entrywise (fun i j => (hA i j).sub continuousAt_const)

/-- Entrywise continuous real matrix families have continuous spectral norm. -/
theorem continuousAt_specNorm_of_entrywise [DecidableEq n]
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x) :
    ContinuousAt (fun y => specNorm (A y)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hF : Filter.Tendsto (fun y => frobNorm (A y - A x)) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, frobNorm_zero] using (continuousAt_frobNorm_sub_of_entrywise hA).tendsto
  have hsmall := hF.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with y hy
  rw [Real.dist_eq]
  exact (abs_specNorm_sub_specNorm_le_frobNorm (A y) (A x)).trans_lt hy

end NLAlib

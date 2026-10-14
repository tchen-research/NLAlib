import NLAlib.Matrix.Perturbation.EigenvaluePerturbation
import NLAlib.Matrix.Norms.Continuity
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of ordered Hermitian eigenvalues

Entrywise matrix continuity implies continuity of every ordered Hermitian
eigenvalue by the spectral perturbation bound and the finite Frobenius sum.
The statement does not select eigenvectors continuously or choose a matrix norm.
-/

noncomputable section
open scoped Topology
namespace NLAlib

variable {E n : Type*} [TopologicalSpace E] [Fintype n] [DecidableEq n]
  {A : E → Matrix n n ℝ} {x : E}

/-- Every ordered eigenvalue of an entrywise continuous Hermitian family is
continuous; repeated eigenvalues and dimension zero require no extra cases. -/
theorem _root_.Matrix.IsHermitian.continuousAt_eigenvalues₀
    (hA : ∀ y, (A y).IsHermitian)
    (hc : ∀ i j, ContinuousAt (fun y => A y i j) x)
    (k : Fin (Fintype.card n)) :
    ContinuousAt (fun y => (hA y).eigenvalues₀ k) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hF : Filter.Tendsto (fun y => frobNorm (A y - A x)) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, frobNorm_zero] using (continuousAt_frobNorm_sub_of_entrywise hc).tendsto
  have hsmall := hF.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with y hy
  rw [Real.dist_eq]
  exact ((abs_eigenvalues₀_sub_le_specNorm_sub (hA x) (hA y) k).trans
    (specNorm_le_frobNorm _)).trans_lt hy

end NLAlib

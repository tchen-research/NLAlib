import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.Matrix

/-!
# Smooth finite matrix inversion

Determinants and adjugates are finite polynomial expressions in matrix entries.
Consequently the total nonsingular inverse is smooth at matrices with nonzero
determinant. This entrywise API avoids choosing a matrix norm instance.
-/

noncomputable section

open Matrix

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
  {r : WithTop ℕ∞} {x : E} {A : E → Matrix ι ι 𝕜}

/-- The determinant of a smooth entrywise matrix family is smooth. -/
theorem ContDiffAt.matrix_det (hA : ∀ i j, ContDiffAt 𝕜 r (fun y => A y i j) x) :
    ContDiffAt 𝕜 r (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply]
  apply ContDiffAt.sum
  intro σ _
  apply ContDiffAt.const_smul
  exact contDiffAt_prod (fun i _ => hA (σ i) i)

/-- Each entry of a smooth matrix family's adjugate is smooth. -/
theorem ContDiffAt.matrix_adjugate_apply
    (hA : ∀ i j, ContDiffAt 𝕜 r (fun y => A y i j) x) (i j : ι) :
    ContDiffAt 𝕜 r (fun y => (A y).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply ContDiffAt.matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hA k l

/-- Each entry of the inverse is smooth wherever the determinant is nonzero. -/
theorem ContDiffAt.matrix_inv_apply
    (hA : ∀ i j, ContDiffAt 𝕜 r (fun y => A y i j) x)
    (hx : (A x).det ≠ 0) (i j : ι) :
    ContDiffAt 𝕜 r (fun y => (A y)⁻¹ i j) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((ContDiffAt.matrix_det hA).inv hx).mul
    (ContDiffAt.matrix_adjugate_apply hA i j)

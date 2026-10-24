import NLAlib.Matrix.Graph.LaplacianResistance

/-!
# Weighted graph Laplacians as finite rank-one sums

The incidence-Gram definition equals the sum of the original edge weights times
the signed-incidence outer products. The formula allows zero output weights and
is used by finite sampled-edge algorithms.

Source: Spielman–Srivastava, Graph Sparsification by Effective Resistances.
-/

noncomputable section
open scoped Matrix

namespace NLAlib.GraphEdgeOrientation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {G : SimpleGraph V} (o : GraphEdgeOrientation G E)

omit [Fintype V] in
/-- A nonnegatively weighted Laplacian is the finite sum of signed-incidence
outer products with the actual edge weights, including zero weights. -/
theorem laplacian_eq_sum_weight_smul_vecMulVec (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    o.laplacian w = ∑ e, w e • Matrix.vecMulVec (o.incidence e) (o.incidence e) := by
  ext a b
  simp only [laplacian, Matrix.mul_apply, Matrix.transpose_apply, weightedIncidence,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = Real.sqrt (w e) ^ 2 * (o.incidence e a * o.incidence e b) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw e)]

omit [Fintype V] in
/-- The zero-weight graph has zero Laplacian, including empty graphs. -/
@[simp] theorem laplacian_zero : o.laplacian (fun _ => 0) = 0 := by
  rw [o.laplacian_eq_sum_weight_smul_vecMulVec _ (fun _ => le_rfl)]
  simp

end NLAlib.GraphEdgeOrientation

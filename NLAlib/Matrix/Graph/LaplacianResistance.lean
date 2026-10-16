import NLAlib.Matrix.Graph.WeightedIncidence
import NLAlib.Matrix.Basic.MoorePenroseProjector
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.Matrix.Basic.QuadForm

/-! # Laplacian resistance and edge leverage

The weighted edge leverage matrix is the orthogonal projector onto the
incidence range. Its diagonal is weighted effective resistance; its trace is
the number of vertices minus the number of components. The result includes
disconnected graphs, isolated vertices, and empty graphs. Resistance is defined
here only for the endpoints of an actual edge, which lie in one component.
Source: Spielman–Srivastava, Graph Sparsification by Effective Resistances.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace NLAlib

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
/-- The Gram-pseudoinverse sandwich is the orthogonal range projector,
including matrices of deficient rank and empty shapes. -/
theorem mul_moorePenroseInverse_gram_mul_transpose (C : Matrix E V ℝ) :
    C * moorePenroseInverse (Cᵀ * C) * Cᵀ = rangeProjector C := by
  have hs := mul_moorePenroseInverse_isHermitian C
  have hp := mul_moorePenroseInverse_isIdempotentElem C
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial C,
    moorePenroseInverse_conjTranspose_mul_self]
  calc
    C * (moorePenroseInverse C * (moorePenroseInverse C)ᴴ) * Cᴴ =
        (C * moorePenroseInverse C) * (C * moorePenroseInverse C)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = C * moorePenroseInverse C := by rw [hs.eq]; exact hp
    _ = rangeProjector C := rfl

namespace GraphEdgeOrientation
variable {G : SimpleGraph V} (o : GraphEdgeOrientation G E)

/-- The weighted graph Laplacian, defined as the weighted incidence Gram matrix. -/
def laplacian (w : E → ℝ) : Matrix V V ℝ :=
  (o.weightedIncidence w)ᵀ * o.weightedIncidence w

/-- Effective resistance between the endpoints of an edge. The vector is the
unweighted signed edge incidence, and no resistance across components is defined. -/
def edgeResistance (w : E → ℝ) (e : E) : ℝ :=
  quadForm (moorePenroseInverse (o.laplacian w)) (o.incidence e)

omit [DecidableEq E] in
/-- The edge leverage matrix is the orthogonal projector onto the weighted
incidence range. No connectedness assumption is imposed.
Source: Spielman–Srivastava.
atlas: laplacian-resistance-leverage (partial) -/
theorem laplacian_leverage_eq_rangeProjector (w : E → ℝ) :
    o.weightedIncidence w * moorePenroseInverse (o.laplacian w) *
      (o.weightedIncidence w)ᵀ = rangeProjector (o.weightedIncidence w) :=
  mul_moorePenroseInverse_gram_mul_transpose _

/-- Weighted effective resistance is exactly the corresponding projector diagonal.
Source: Spielman–Srivastava.
atlas: laplacian-resistance-leverage (partial) -/
theorem weight_mul_edgeResistance_eq_diag (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (e : E) :
    w e * o.edgeResistance w e = rangeProjector (o.weightedIncidence w) e e := by
  rw [← o.laplacian_leverage_eq_rangeProjector]
  have hdiag : (o.weightedIncidence w * moorePenroseInverse (o.laplacian w) *
      (o.weightedIncidence w)ᵀ) e e =
      quadForm (moorePenroseInverse (o.laplacian w)) (o.weightedIncidence w e) := by
    rw [quadForm_def, star_trivial, Matrix.dotProduct_mulVec]
    rfl
  rw [hdiag]
  have hrow : o.weightedIncidence w e = Real.sqrt (w e) • o.incidence e := rfl
  rw [hrow, quadForm_smul, star_trivial, ← pow_two, Real.sq_sqrt (hw e)]
  rfl

/-- Every edge leverage lies between zero and one.
Source: Spielman–Srivastava.
atlas: laplacian-resistance-leverage (partial) -/
theorem weight_mul_edgeResistance_mem_Icc (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (e : E) :
    w e * o.edgeResistance w e ∈ Set.Icc (0 : ℝ) 1 := by
  rw [o.weight_mul_edgeResistance_eq_diag w hw]
  exact re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem (rangeProjector (o.weightedIncidence w))
    (rangeProjector_isHermitian (o.weightedIncidence w))
    (rangeProjector_isIdempotentElem (o.weightedIncidence w)) e

omit [DecidableEq E] in
/-- The Laplacian rank is `|V| - number of connected components`, including
isolated vertices and all empty dimensions.
Source: Chung, Chapter 1.
atlas: laplacian-resistance-leverage (partial) -/
theorem rank_laplacian (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    (o.laplacian w).rank = Fintype.card V - Nat.card G.ConnectedComponent := by
  rw [laplacian, Matrix.rank_transpose_mul_self, o.rank_weightedIncidence w hw]

/-- Foster's identity: weighted edge resistances sum to the Laplacian rank,
and hence to vertices minus connected components. This includes disconnected
graphs and isolates, and evaluates to zero for an empty edge set.
Source: Spielman–Srivastava.
atlas: laplacian-resistance-leverage (partial) -/
theorem sum_weight_mul_edgeResistance (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    (∑ e, w e * o.edgeResistance w e) = ((o.laplacian w).rank : ℝ) ∧
    (∑ e, w e * o.edgeResistance w e) =
      ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ) := by
  have hsum : (∑ e, w e * o.edgeResistance w e) =
      ((o.weightedIncidence w).rank : ℝ) := by
    simp_rw [o.weight_mul_edgeResistance_eq_diag w (fun e => (hw e).le)]
    exact trace_mul_moorePenroseInverse _
  constructor
  · rw [hsum, laplacian, Matrix.rank_transpose_mul_self]
  · rw [hsum, o.rank_weightedIncidence w hw]

end GraphEdgeOrientation
end NLAlib

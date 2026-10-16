import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Weighted incidence matrices and connected components

An orientation records the endpoints of each edge and covers precisely the
adjacencies of the underlying finite undirected graph. Parallel edge records
are harmless. The kernel consists exactly of componentwise constant vectors,
so the rank formula includes isolated vertices and empty graphs.
Source: Chung, Spectral Graph Theory, Chapter 1.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace NLAlib

/-- An orientation of edge records of an undirected loop-free graph.
`complete` says every graph edge has a record in one of its two orientations. -/
structure GraphEdgeOrientation {V : Type*} (G : SimpleGraph V) (E : Type*) where
  /-- Initial endpoint of an oriented edge. -/
  source : E → V
  /-- Final endpoint of an oriented edge. -/
  target : E → V
  /-- Every record is an actual edge, so loops are excluded. -/
  adjacent : ∀ e, G.Adj (source e) (target e)
  /-- Every undirected edge occurs among the edge records. -/
  complete : ∀ {u v}, G.Adj u v → ∃ e,
    (source e = u ∧ target e = v) ∨ (source e = v ∧ target e = u)

namespace GraphEdgeOrientation
variable {V E : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} (o : GraphEdgeOrientation G E)

/-- The signed incidence matrix of an orientation, with one row per edge. -/
def incidence : Matrix E V ℝ := fun e v =>
  (if o.source e = v then 1 else 0) - (if o.target e = v then 1 else 0)

/-- The weighted incidence matrix `diag(√w) B`. -/
def weightedIncidence (w : E → ℝ) : Matrix E V ℝ :=
  fun e v => Real.sqrt (w e) * o.incidence e v

/-- Incidence multiplication computes oriented endpoint differences. -/
theorem incidence_mulVec (x : V → ℝ) (e : E) :
    (o.incidence *ᵥ x) e = x (o.source e) - x (o.target e) := by
  simp [incidence, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- Weighted incidence multiplication computes weighted endpoint differences. -/
theorem weightedIncidence_mulVec (w : E → ℝ) (x : V → ℝ) (e : E) :
    (o.weightedIncidence w *ᵥ x) e =
      Real.sqrt (w e) * (x (o.source e) - x (o.target e)) := by
  change (∑ v, (Real.sqrt (w e) * o.incidence e v) * x v) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  exact congrArg (Real.sqrt (w e) * ·) (o.incidence_mulVec x e)

/-- With strictly positive weights, the weighted incidence kernel imposes
equality at exactly the pairs of adjacent vertices. -/
theorem weightedIncidence_mulVec_eq_zero_iff (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (x : V → ℝ) : o.weightedIncidence w *ᵥ x = 0 ↔
      ∀ u v, G.Adj u v → x u = x v := by
  constructor
  · intro hx u v huv
    obtain ⟨e, he | he⟩ := o.complete huv
    all_goals
      have hz := congrFun hx e
      rw [o.weightedIncidence_mulVec] at hz
      have hdiff := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
        (Real.sqrt_pos.mpr (hw e)).ne')
    · simpa only [he.1, he.2] using hdiff
    · simpa only [he.1, he.2] using hdiff.symm
  · intro hx
    funext e
    rw [o.weightedIncidence_mulVec, hx _ _ (o.adjacent e), sub_self, mul_zero]
    rfl

omit [Fintype V] [DecidableEq V] in
/-- Equality along graph edges propagates along every finite walk. -/
theorem eq_of_reachable {x : V → ℝ} (hx : ∀ u v, G.Adj u v → x u = x v)
    {u v : V} (h : G.Reachable u v) : x u = x v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (hx _ _ hadj).trans ih

/-- Componentwise constants are linearly equivalent to the weighted incidence kernel.
This explicit quotient lift identifies all kernel vectors, including isolated vertices. -/
def componentKernelEquiv (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    (G.ConnectedComponent → ℝ) ≃ₗ[ℝ] LinearMap.ker (o.weightedIncidence w).mulVecLin where
  toFun f := ⟨fun v => f (G.connectedComponentMk v),
    (o.weightedIncidence_mulVec_eq_zero_iff w hw _).mpr
      (fun u v huv => congrArg f (SimpleGraph.ConnectedComponent.sound huv.reachable))⟩
  invFun x := Quot.lift x.val (fun _ _ h =>
    eq_of_reachable ((o.weightedIncidence_mulVec_eq_zero_iff w hw x.val).mp x.property) h)
  left_inv f := by
    funext c
    exact SimpleGraph.ConnectedComponent.ind (fun _ => rfl) c
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' a f := by
    apply Subtype.ext
    rfl

/-- Rank of a weighted incidence matrix: number of vertices minus number of
connected components. Positive weights and any orientation give the same rank.
Source: Chung, Chapter 1.
atlas: laplacian-resistance-leverage (partial) -/
theorem rank_weightedIncidence [Fintype E] (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    (o.weightedIncidence w).rank = Fintype.card V - Nat.card G.ConnectedComponent := by
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hk : Module.finrank ℝ (LinearMap.ker (o.weightedIncidence w).mulVecLin) =
      Fintype.card G.ConnectedComponent := by
    rw [← (o.componentKernelEquiv w hw).finrank_eq]
    exact Module.finrank_fintype_fun_eq_card ℝ
  have hr := (o.weightedIncidence w).mulVecLin.finrank_range_add_finrank_ker
  rw [hk, Module.finrank_fintype_fun_eq_card] at hr
  rw [Nat.card_eq_fintype_card]
  change Module.finrank ℝ (LinearMap.range (o.weightedIncidence w).mulVecLin) = _
  omega

end GraphEdgeOrientation
end NLAlib

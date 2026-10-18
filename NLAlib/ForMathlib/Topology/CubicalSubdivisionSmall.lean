import NLAlib.ForMathlib.Topology.CubicalSubdivision
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Uniformly small actual subedges of a continuous path

Compactness of the unit interval supplies a genuine finite uniform
subdivision whose whole subedges lie close to their initial points. This
uses only continuity, so it can be combined with finite-chain subdivision
without changing corners or requiring nonzero derivatives.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

/-- The actual linearly interpolated parameter of a uniform subedge is no
farther than one mesh width from that subedge's initial parameter. -/
theorem dist_convexComb_uniformNode_le {n i : ℕ} (hn : 0 < n) (hi : i < n) (t : I) :
    dist (Set.Icc.convexComb (uniformNode n i) (uniformNode n (i + 1)) t) (uniformNode n i) ≤
      1 / (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [Set.Icc.coe_convexComb, coe_uniformNode_of_le hn hi.le,
    coe_uniformNode_of_le hn (Nat.succ_le_of_lt hi), Nat.cast_succ]
  have he : (1 - (t : ℝ)) * ((i : ℝ) / n) + (t : ℝ) * (((i : ℝ) + 1) / n) -
      (i : ℝ) / n = (t : ℝ) / n := by ring
  rw [he, abs_of_nonneg (div_nonneg t.property.1 hn'.le)]
  exact div_le_div_of_nonneg_right t.property.2 hn'.le

/-- Every continuous path in a normed group has an actual positive uniform
subdivision with every point of each subedge within `ε` of its initial point. -/
theorem exists_uniform_subdivision_image_small
    {E : Type*} [NormedAddCommGroup E] (γ : C(I, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ t : I,
      ‖subedge γ (uniformNode n i) (uniformNode n (i + 1)) t - γ (uniformNode n i)‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  intro i hi t
  have hm' : 1 / ((m + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  have hd := (dist_convexComb_uniformNode_le (Nat.succ_pos m) hi t).trans_lt hm'
  change ‖γ (Set.Icc.convexComb (uniformNode (m + 1) i) (uniformNode (m + 1) (i + 1)) t) -
    γ (uniformNode (m + 1) i)‖ < ε
  simpa only [dist_eq_norm] using hsmall hd

end Cubical

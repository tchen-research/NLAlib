import NLAlib.ForMathlib.Topology.RectangularGridWalkGeometry
import NLAlib.ForMathlib.Topology.CubicalContractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Topology.MetricSpace.Thickening

/-! # Actual local fillings between short paths and finite grid walks

Join each original endpoint to its specified nearby grid vertex. The short
original path, two connectors and finite canonical grid walk form an actual
cycle. All active paths lie in a small convex ball, whose actual contraction
constructs a finite normalized filling. No differentiability is needed for
this topological comparison.
-/

noncomputable section
open Set Metric
open scoped unitInterval
namespace Cubical.RectangularGrid
variable {m n : ℕ} {C : Set ℂ}

/-- The actual straight connector from a trace point to its specified grid vertex. -/
def quantizerConnector (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (z : C) : C(I, ℂ) :=
  (Path.segment (z : ℂ) (vertex x y (q z).1 (q z).2)).toContinuousMap

/-- The actual closed comparison chain of one short original path and
the finite L-shaped canonical grid walk between its quantized endpoints. -/
def localComparisonChain (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (γ : C(I, C)) : OneChain ℂ :=
  Finsupp.single ((⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)).comp γ) 1 +
    Finsupp.single (quantizerConnector x y q (γ 1)) 1 -
    Grid.walkChain (vertex x y) (q (γ 0)) (q (γ 1)) -
    Finsupp.single (quantizerConnector x y q (γ 0)) 1

/-- The original subpath, connectors and actual finite grid walk have
exactly zero native endpoint boundary. -/
theorem boundaryOne_localComparisonChain
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (γ : C(I, C)) :
    boundaryOne (localComparisonChain x y q γ) = 0 := by
  rw [localComparisonChain, map_sub, map_sub, map_add, Grid.boundaryOne_walkChain]
  simp only [boundaryOne, Finsupp.linearCombination_single, one_smul,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, quantizerConnector,
    Path.coe_toContinuousMap, Path.source, Path.target]
  abel

/-- All active paths of the actual local comparison lie in a controlled
ball around the original initial point. The quantizer is allowed to be discontinuous. -/
theorem localComparisonChain_mapsTo_ball
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x) (hy : Monotone y)
    (q : C → Fin (m + 1) × Fin (n + 1)) {h : ℝ} (hh : 0 < h)
    (hq : ∀ z : C, ‖vertex x y (q z).1 (q z).2 - z‖ < 2 * h)
    (γ : C(I, C)) (hγ : ∀ t, ‖(γ t : ℂ) - γ 0‖ < h) :
    ∀ δ ∈ (localComparisonChain x y q γ).support, ∀ t,
      δ t ∈ ball (γ 0 : ℂ) (8 * h) := by
  let B : Set ℂ := ball (γ 0 : ℂ) (8 * h)
  let P : Submodule ℤ (OneChain ℂ) := Finsupp.supported ℤ ℤ {δ : C(I, ℂ) | ∀ t, δ t ∈ B}
  have h0 : (γ 0 : ℂ) ∈ B := by
    simp only [B, mem_ball, dist_self]
    positivity
  have h1 : (γ 1 : ℂ) ∈ B := by
    rw [mem_ball, dist_eq_norm]
    exact (hγ 1).trans (by linarith)
  have hq0 : ‖vertex x y (q (γ 0)).1 (q (γ 0)).2 - γ 0‖ < 3 * h :=
    (hq (γ 0)).trans (by linarith)
  have hq1 : ‖vertex x y (q (γ 1)).1 (q (γ 1)).2 - γ 0‖ < 3 * h := by
    exact (norm_sub_le_norm_sub_add_norm_sub _ (γ 1 : ℂ) _).trans_lt
      (by linarith [hq (γ 1), hγ 1])
  have hQ0 : vertex x y (q (γ 0)).1 (q (γ 0)).2 ∈ B := by
    rw [mem_ball, dist_eq_norm]
    exact hq0.trans (by linarith)
  have hQ1 : vertex x y (q (γ 1)).1 (q (γ 1)).2 ∈ B := by
    rw [mem_ball, dist_eq_norm]
    exact hq1.trans (by linarith)
  have hsingle : Finsupp.single
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)).comp γ) (1 : ℤ) ∈ P := by
    apply Finsupp.single_mem_supported
    intro t
    rw [mem_ball, dist_eq_norm]
    exact (hγ t).trans (by linarith)
  have hc0 : Finsupp.single (quantizerConnector x y q (γ 0)) (1 : ℤ) ∈ P := by
    apply Finsupp.single_mem_supported
    intro t
    exact (convex_ball _ _).lineMap_mem h0 hQ0 t.property
  have hc1 : Finsupp.single (quantizerConnector x y q (γ 1)) (1 : ℤ) ∈ P := by
    apply Finsupp.single_mem_supported
    intro t
    exact (convex_ball _ _).lineMap_mem h1 hQ1 t.property
  have hwalk : Grid.walkChain (vertex x y) (q (γ 0)) (q (γ 1)) ∈ P := by
    intro δ hδ t
    rw [mem_ball, dist_eq_norm]
    have hw := walkChain_norm_sub_lt x y hx hy _ _ hq0 hq1 δ hδ t
    exact hw.trans (by linarith)
  exact P.sub_mem (P.sub_mem (P.add_mem hsingle hc1) hwalk) hc0

/-- The actual comparison of a sufficiently short path with its finite
canonical grid walk bounds a finite normalized two-chain in a small ball.
This is a genuine local straight-line contraction, with no assumed homotopy or period. -/
theorem exists_isNullHomologous_mapOne_eq_localComparisonChain
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x) (hy : Monotone y)
    (q : C → Fin (m + 1) × Fin (n + 1)) {h : ℝ} (hh : 0 < h)
    (hq : ∀ z : C, ‖vertex x y (q z).1 (q z).2 - z‖ < 2 * h)
    (γ : C(I, C)) (hγ : ∀ t, ‖(γ t : ℂ) - γ 0‖ < h) :
    ∃ Δ : OneChain (ball (γ 0 : ℂ) (8 * h)),
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
        C(ball (γ 0 : ℂ) (8 * h), ℂ)) Δ = localComparisonChain x y q γ ∧
          IsNullHomologous Δ := by
  let : ContractibleSpace (ball (γ 0 : ℂ) (8 * h)) :=
    (convex_ball _ _).contractibleSpace ⟨γ 0, by simp; positivity⟩
  exact exists_isNullHomologous_mapOne_subtype_val_eq _ _
    (boundaryOne_localComparisonChain x y q γ)
    (localComparisonChain_mapsTo_ball x y hx hy q hh hq γ hγ)

/-- The same explicit local filling lies in a common small neighborhood of
the original trace. This common domain permits finite sums of the fillings
while keeping every actual square close to that trace. -/
theorem exists_isNullHomologous_mapOne_eq_localComparisonChain_thickening
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x) (hy : Monotone y)
    (q : C → Fin (m + 1) × Fin (n + 1)) {h : ℝ} (hh : 0 < h)
    (hq : ∀ z : C, ‖vertex x y (q z).1 (q z).2 - z‖ < 2 * h)
    (γ : C(I, C)) (hγ : ∀ t, ‖(γ t : ℂ) - γ 0‖ < h) :
    ∃ Δ : OneChain (thickening (8 * h) C),
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
        C(thickening (8 * h) C, ℂ)) Δ = localComparisonChain x y q γ ∧
          IsNullHomologous Δ := by
  obtain ⟨Δ, hΔ, hnull⟩ := exists_isNullHomologous_mapOne_eq_localComparisonChain
    x y hx hy q hh hq γ hγ
  have hB : ball (γ 0 : ℂ) (8 * h) ⊆ thickening (8 * h) C := by
    intro z hz
    exact mem_thickening_iff.mpr ⟨γ 0, (γ 0).property, hz⟩
  refine ⟨mapOne (ContinuousMap.inclusion hB) Δ, ?_, hnull.map _⟩
  rw [mapOne_mapOne]
  exact hΔ

end Cubical.RectangularGrid

import NLAlib.ForMathlib.Topology.RectangularGridApproximation
import NLAlib.ForMathlib.Topology.RectangularGridQuantization

/-! # Actual finite grid approximation of a continuous cycle

The local edge fillings assemble linearly. Their endpoint connectors cancel
against the native endpoint boundary of the cycle, leaving an actual
normalized filling of the difference from a finite grid cycle.
-/

noncomputable section
open Set Metric
open scoped unitInterval
namespace Cubical.RectangularGrid
variable {m n : ℕ} {C : Set ℂ}

/-- Extend the actual endpoint-to-grid connectors linearly to endpoint chains. -/
def connectorChainMap (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) : (C →₀ ℤ) →ₗ[ℤ] OneChain ℂ :=
  Finsupp.linearCombination ℤ (fun z => Finsupp.single (quantizerConnector x y q z) 1)

/-- The connector map of an edge boundary is exactly its final connector
minus its initial connector. -/
theorem connectorChainMap_boundaryOne_single
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (γ : C(I, C)) (k : ℤ) :
    connectorChainMap x y q (boundaryOne (Finsupp.single γ k)) =
      k • Finsupp.single (quantizerConnector x y q (γ 1)) 1 -
        k • Finsupp.single (quantizerConnector x y q (γ 0)) 1 := by
  simp [boundaryOne, connectorChainMap, smul_sub]

/-- A continuous finite cycle is homologous to an actual canonical grid
cycle, through a filling lying in the small neighborhood of its trace.
The finite integer arrays are constructed from actual uniform subdivisions
and actual quantized endpoint walks. -/
theorem exists_isNullHomologous_mapOne_eq_cycleComparison
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hy : StrictMono y)
    (q : C → Fin (m + 1) × Fin (n + 1)) {h : ℝ} (hh : 0 < h)
    (hq : ∀ z : C, ‖vertex x y (q z).1 (q z).2 - z‖ < 2 * h)
    (Γ : OneChain C) (hc : boundaryOne Γ = 0) :
    ∃ c : Grid.Coefficients m n, ∃ Δ : OneChain (thickening (8 * h) C),
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
        C(thickening (8 * h) C, ℂ)) Δ =
          mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) Γ -
            Grid.edgeChainMap (vertex x y) c ∧
        IsNullHomologous Δ ∧ RectangularChain.IsCycle c.1 c.2 := by
  classical
  choose c d he hd using
    exists_isNullHomologous_mapOne_eq_edgeComparison x y hx.monotone hy.monotone q hh hq
  let cm : OneChain C →ₗ[ℤ] Grid.Coefficients m n := Finsupp.linearCombination ℤ c
  let dm : OneChain C →ₗ[ℤ] OneChain (thickening (8 * h) C) :=
    Finsupp.linearCombination ℤ d
  let j : C(C, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let incl : C(thickening (8 * h) C, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hnull (Ξ : OneChain C) : IsNullHomologous (dm Ξ) := by
    induction Ξ using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (isNullHomologous_zero (X := thickening (8 * h) C))
    | add Ξ Θ hΞ hΘ => simpa only [map_add] using hΞ.add hΘ
    | single γ k => simpa only [dm, Finsupp.linearCombination_single] using (hd γ).smul k
  have heq (Ξ : OneChain C) : mapOne incl (dm Ξ) =
      mapOne j Ξ + connectorChainMap x y q (boundaryOne Ξ) -
        Grid.edgeChainMap (vertex x y) (cm Ξ) := by
    induction Ξ using Finsupp.induction_linear with
    | zero => simp
    | add Ξ Θ hΞ hΘ =>
      simp only [map_add, hΞ, hΘ]
      abel
    | single γ k =>
      simp only [dm, cm, Finsupp.linearCombination_single, map_smul, mapOne_single,
        connectorChainMap_boundaryOne_single]
      rw [he γ]
      simp only [smul_sub, smul_add, Finsupp.smul_single_one]
      abel
  have hdiff : mapOne incl (dm Γ) = mapOne j Γ -
      Grid.edgeChainMap (vertex x y) (cm Γ) := by
    simpa only [hc, map_zero, add_zero] using heq Γ
  refine ⟨cm Γ, dm Γ, hdiff, hnull Γ, ?_⟩
  apply Grid.isCycle_of_boundaryOne_edgeChain_eq_zero (vertex x y) (vertex_injective x y hx hy)
  have hb := (hnull Γ).boundaryOne_eq_zero
  have hb' : boundaryOne (mapOne incl (dm Γ)) = 0 := by
    rw [boundaryOne_mapOne, hb, map_zero]
  rw [hdiff, map_sub, boundaryOne_mapOne, hc, map_zero, zero_sub, neg_eq_zero] at hb'
  exact hb'

/-- Compactness supplies an actual finite uniform rectangular grid and a
cycle approximation with an actual close normalized filling. -/
theorem exists_uniform_grid_cycle_approximation (hC : IsCompact C) {h : ℝ} (hh : 0 < h)
    (Γ : OneChain C) (hc : boundaryOne Γ = 0) :
    ∃ N : ℕ, ∃ c : Grid.Coefficients (2 * N) (2 * N),
      ∃ Δ : OneChain (thickening (8 * h) C),
        mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
          C(thickening (8 * h) C, ℂ)) Δ =
            mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) Γ -
              Grid.edgeChainMap (vertex (coordinate N h) (coordinate N h)) c ∧
          IsNullHomologous Δ ∧ RectangularChain.IsCycle c.1 c.2 := by
  obtain ⟨N, q, hq⟩ := exists_quantizer hC hh
  obtain ⟨c, Δ, he, hn, hc'⟩ := exists_isNullHomologous_mapOne_eq_cycleComparison
    (coordinate N h) (coordinate N h) (strictMono_coordinate N hh) (strictMono_coordinate N hh)
    q hh hq Γ hc
  exact ⟨N, c, Δ, he, hn, hc'⟩

end Cubical.RectangularGrid

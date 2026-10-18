import NLAlib.ForMathlib.Analysis.Complex.CubicalGridWindingComparison
import NLAlib.ForMathlib.Analysis.Complex.CubicalWindingVariation
import NLAlib.ForMathlib.Topology.BoundedComplementFill
import NLAlib.ForMathlib.Topology.RectangularGridCycleApproximation
import NLAlib.ForMathlib.Topology.RectangularGridCellBounds

/-! # Support of the actual finite grid filling

Outside the bounded-complement fill of the original trace, actual winding
vanishes. The close comparison preserves that winding at every sufficiently
distant cell center. Exact cell-coefficient isolation therefore forces all
cells needed by the finite filling to remain inside the specified open
neighborhood of the filled trace.
-/

noncomputable section
open Set Metric Bornology
open scoped unitInterval
namespace Complex
open Cubical Cubical.RectangularGrid

/-- A cycle contained in `C` has zero actual winding outside the fill of
`C`, even when `C` contains additional points beyond its actual trace. -/
theorem cubicalWindingIntegral_eq_zero_of_not_mem_boundedComplementFill
    {C : Set ℂ} (Γ : OneChain C) (hc : boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {τ : ℂ} (hτ : τ ∉ boundedComplementFill C) : cubicalWindingIntegral Γ τ = 0 := by
  obtain ⟨hoff, hunbounded⟩ := not_mem_boundedComplementFill_iff.mp hτ
  apply cubicalWindingIntegral_eq_zero_of_unbounded_preconnected Γ hc hΓ
    isPreconnected_connectedComponentIn (S := connectedComponentIn Cᶜ τ)
    (fun z hz => fun ht => connectedComponentIn_subset Cᶜ τ hz (cubicalTrace_subset Γ ht))
    hunbounded (mem_connectedComponentIn hoff)

/-- Every nonzero prefix cell of an actual close grid approximation is
inside the desired neighborhood of the compact filled trace. Its coefficient
is obtained from actual winding; no support or period conclusion is assumed. -/
theorem rectangularGrid_cell_mem_of_comparison
    {C Ω : Set ℂ} (Γ : OneChain C) (hc : boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {h δ : ℝ} (hh : 0 < h) (hmesh : 9 * h ≤ δ)
    (hbuffer : cthickening δ (boundedComplementFill C) ⊆ Ω)
    (N : ℕ) (c : Grid.Coefficients (2 * N) (2 * N))
    (hcycle : RectangularChain.IsCycle c.1 c.2)
    (Δ : OneChain (thickening (8 * h) C)) (hnull : IsNullHomologous Δ)
    (he : mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
        C(thickening (8 * h) C, ℂ)) Δ =
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) Γ -
        Grid.edgeChainMap (vertex (coordinate N h) (coordinate N h)) c) :
    ∀ i j, RectangularChain.cellCoefficients c.1 i j ≠ 0 →
      ∀ p, Grid.cell (vertex (coordinate N h) (coordinate N h)) i j p ∈ Ω := by
  intro i j hij p
  let τ := center (coordinate N h) (coordinate N h) i j
  have hnear : τ ∈ thickening (8 * h) (boundedComplementFill C) := by
    by_contra hnot
    have hofffill : τ ∉ boundedComplementFill C :=
      fun ht => hnot (self_subset_thickening (by positivity) _ ht)
    have hoff : τ ∉ thickening (8 * h) C := by
      intro ht
      obtain ⟨z, hz, hd⟩ := mem_thickening_iff.mp ht
      exact hnot (mem_thickening_iff.mpr ⟨z, subset_boundedComplementFill C hz, hd⟩)
    have hz := cubicalWindingIntegral_eq_zero_of_not_mem_boundedComplementFill Γ hc hΓ hofffill
    have heq := cubicalWindingIntegral_eq_grid_of_isNullHomologous_comparison Γ hΓ
      (vertex (coordinate N h) (coordinate N h)) c.1 c.2 Δ hnull he isOpen_thickening hoff
    have hi := cubicalWindingIntegral_rectangularGrid_eq_cellCoefficients
      (coordinate N h) (coordinate N h) (strictMono_coordinate N hh) (strictMono_coordinate N hh)
      c.1 c.2 hcycle i j
    change cubicalWindingIntegral (mapOne fullPlaneLift
      (Grid.edgeChain (vertex (coordinate N h) (coordinate N h)) c.1 c.2)) τ = _ at hi
    have hzero : ((RectangularChain.cellCoefficients c.1 i j : ℤ) : ℂ) = 0 := by
      rw [← hi, ← heq, hz]
    exact hij (by exact_mod_cast hzero)
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.mp hnear
  apply hbuffer
  apply mem_cthickening_of_dist_le _ z δ _ hz
  have hcell := norm_cell_sub_center_le (coordinate N h) (coordinate N h)
    (strictMono_coordinate N hh).monotone (strictMono_coordinate N hh).monotone i j
    (coordinate_succ_sub_castSucc N h i).le (coordinate_succ_sub_castSucc N h j).le p
  rw [dist_eq_norm] at hd ⊢
  exact (norm_sub_le_norm_sub_add_norm_sub _ τ z).trans (by linarith)

end Complex

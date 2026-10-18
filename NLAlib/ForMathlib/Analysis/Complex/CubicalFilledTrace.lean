import NLAlib.ForMathlib.Analysis.Complex.CubicalGridFillingSupport

/-! # Actual finite cubical fillings inside a planar filled trace neighborhood

A continuous finite C1 cycle bounds an actual finite normalized cubical
two-chain in every open neighborhood of its trace and bounded complementary
components. The proof constructs a sufficiently fine grid comparison,
identifies its coefficients by actual winding and fills exactly its nonzero
cells. It does not assume a contraction, Cauchy formula, or spectral period.

For a Jordan contour the bounded-complement fill is its usual closed
interior. The construction also works for arbitrary finite cycles and does
not require injectivity, a smooth global concatenation, or nonzero velocities.
-/

noncomputable section
open Set Metric
open scoped unitInterval
namespace Complex
open Cubical Cubical.RectangularGrid

/-- A finite piecewise C1 cycle in a compact planar set has an actual
normalized finite filling in every open neighborhood of that set and its
bounded complementary components. -/
theorem exists_isNullHomologous_mapOne_eq_of_boundedComplementFill_subset
    {C Ω : Set ℂ} (hC : IsCompact C) (hΩ : IsOpen Ω)
    (hfill : boundedComplementFill C ⊆ Ω)
    (Γ : OneChain C) (hc : boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I) :
    ∃ Φ : OneChain Ω,
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(Ω, ℂ)) Φ =
        mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) Γ ∧ IsNullHomologous Φ := by
  obtain ⟨δ, hδ, hbuffer⟩ :=
    exists_cthickening_boundedComplementFill_subset_open hC hΩ hfill
  let h : ℝ := δ / 32
  have hh : 0 < h := div_pos hδ (by norm_num)
  have hmesh : 9 * h ≤ δ := by dsimp [h]; linarith
  obtain ⟨N, c, Δ, he, hn, hcycle⟩ := exists_uniform_grid_cycle_approximation hC hh Γ hc
  have hcells := rectangularGrid_cell_mem_of_comparison Γ hc hΓ hh hmesh hbuffer
    N c hcycle Δ hn he
  obtain ⟨Ψ, hΨ, hnΨ⟩ := Grid.exists_isNullHomologous_mapOne_eq_edgeChain
    (vertex (coordinate N h) (coordinate N h)) c.1 c.2 hcycle Ω hcells
  have hnear : thickening (8 * h) C ⊆ Ω := by
    intro z hz
    obtain ⟨w, hw, hd⟩ := mem_thickening_iff.mp hz
    apply hbuffer
    exact mem_cthickening_of_dist_le z w δ (boundedComplementFill C)
      (subset_boundedComplementFill C hw) (hd.le.trans (by linarith))
  let incl : C(thickening (8 * h) C, Ω) := ContinuousMap.inclusion hnear
  refine ⟨mapOne incl Δ + Ψ, ?_, (hn.map incl).add hnΨ⟩
  have hj : (⟨Subtype.val, continuous_subtype_val⟩ : C(Ω, ℂ)).comp incl =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(thickening (8 * h) C, ℂ)) := by ext z; rfl
  rw [map_add, mapOne_mapOne, hj, he, hΨ]
  exact sub_add_cancel _ _

/-- Every native finite C1 cycle is actually null-homologous in an open
domain containing its compact filled trace. This supplies the missing
topological premise of the general contour Cauchy and Gauss theorems from
the stated geometric neighborhood hypothesis.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem isNullHomologous_of_boundedComplementFill_cubicalTrace_subset
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (Γ : OneChain Ω) (hc : boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hfill : boundedComplementFill (cubicalTrace Γ) ⊆ Ω) : IsNullHomologous Γ := by
  let C := cubicalTrace Γ
  let jΩ : C(Ω, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hs : ∀ γ ∈ (mapOne jΩ Γ).support, ∀ t, γ t ∈ C :=
    mapOne_mem_supported jΩ Γ _ (fun γ hγ t => mem_cubicalTrace hγ t)
  obtain ⟨ΓC, hΓC⟩ := exists_mapOne_subtype_val_eq (mapOne jΩ Γ) C hs
  have hCΩ : C ⊆ Ω := cubicalTrace_subset Γ
  let incl : C(C, Ω) := ContinuousMap.inclusion hCΩ
  have he : mapOne incl ΓC = Γ := by
    apply mapOne_injective jΩ Subtype.val_injective
    rw [mapOne_mapOne]
    exact hΓC
  have hcC : boundaryOne ΓC = 0 := by
    apply mapZero_injective incl (by intro a b hab; exact Subtype.ext (congrArg
      (fun z : Ω => (z : ℂ)) hab))
    rw [← boundaryOne_mapOne, he, hc, map_zero]
  have hregC : ∀ γ ∈ ΓC.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I := by
    intro γ hγ
    have hmem := (mem_support_mapOne_comp_iff incl
      (by intro a b hab; exact Subtype.ext (congrArg (fun z : Ω => (z : ℂ)) hab)) ΓC γ).mpr hγ
    rw [he] at hmem
    exact hΓ _ hmem
  obtain ⟨Φ, hΦ, hnΦ⟩ := exists_isNullHomologous_mapOne_eq_of_boundedComplementFill_subset
    (isCompact_cubicalTrace Γ) hΩ hfill ΓC hcC hregC
  have heΦ : Φ = Γ := mapOne_injective jΩ Subtype.val_injective (hΦ.trans hΓC)
  exact heΦ ▸ hnΦ

end Complex

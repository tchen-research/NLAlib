import NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralMaps
import NLAlib.ForMathlib.Analysis.Complex.RectangularGridWinding
import NLAlib.ForMathlib.Topology.CubicalSupportMaps
import NLAlib.ForMathlib.Topology.CubicalGridLinear
import NLAlib.ForMathlib.Analysis.Calculus.Path

/-! # Winding preservation through an actual close grid filling

An actual normalized filling of the difference of a piecewise smooth cycle
and a canonical grid cycle preserves their actual native winding outside
the filling domain. Regularity of the comparison chain follows from its
actual boundary-chain equality, not from smoothness of the filling squares.
-/

noncomputable section
open Set
open scoped unitInterval
namespace Complex

/-- The canonical continuous lift of the complex plane to the full-plane
domain subtype, for the native cubical contour integration interface. -/
def fullPlaneLift : C(ℂ, (univ : Set ℂ)) :=
  ⟨fun z => ⟨z, mem_univ z⟩, continuous_id.subtype_mk _⟩

/-- Every active canonical grid edge is smooth in its native parameter,
independently of cancellation or repeated grid vertices. -/
theorem contDiffOn_cubicalPath_grid_edgeChain
    {m n : ℕ} (v : Fin (m + 1) → Fin (n + 1) → ℂ)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ) :
    ∀ γ ∈ (Cubical.mapOne fullPlaneLift (Cubical.Grid.edgeChain v h w)).support,
      ContDiffOn ℝ 1 (cubicalPath γ).extend I := by
  apply Cubical.mapOne_mem_supported
  have hs := Cubical.Grid.edgeChain_mem_supported v h w
    {γ : C(I, ℂ) | ContDiffOn ℝ 1 (cubicalPath (fullPlaneLift.comp γ)).extend I}
    (by
      intro i j _
      change ContDiffOn ℝ 1 (Path.segment (v i.castSucc j) (v i.succ j)).extend I
      exact Path.contDiffOn_extend_segment _ _ _)
    (by
      intro i j _
      change ContDiffOn ℝ 1 (Path.segment (v i j.castSucc) (v i j.succ)).extend I
      exact Path.contDiffOn_extend_segment _ _ _)
  exact hs

/-- A true normalized comparison filling preserves native winding outside
its open domain. Original and grid edges need only be piecewise C1; no
regularity is imposed on the actual two-dimensional filling. -/
theorem cubicalWindingIntegral_eq_grid_of_isNullHomologous_comparison
    {C Θ : Set ℂ} (Γ : Cubical.OneChain C)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {m n : ℕ} (v : Fin (m + 1) → Fin (n + 1) → ℂ)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (Δ : Cubical.OneChain Θ) (hnull : Cubical.IsNullHomologous Δ)
    (he : Cubical.mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(Θ, ℂ)) Δ =
      Cubical.mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) Γ -
        Cubical.Grid.edgeChain v h w)
    (hΘ : IsOpen Θ) {τ : ℂ} (hτ : τ ∉ Θ) :
    cubicalWindingIntegral Γ τ =
      cubicalWindingIntegral (Cubical.mapOne fullPlaneLift (Cubical.Grid.edgeChain v h w)) τ := by
  let jC : C(C, (univ : Set ℂ)) := ContinuousMap.inclusion (subset_univ C)
  let jΘ : C(Θ, (univ : Set ℂ)) := ContinuousMap.inclusion (subset_univ Θ)
  have hjC : fullPlaneLift.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)) = jC := by
    ext z
    rfl
  have hjΘ : fullPlaneLift.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(Θ, ℂ)) = jΘ := by
    ext z
    rfl
  have he' : Cubical.mapOne jΘ Δ = Cubical.mapOne jC Γ -
      Cubical.mapOne fullPlaneLift (Cubical.Grid.edgeChain v h w) := by
    have hp := congrArg (Cubical.mapOne fullPlaneLift) he
    simpa only [map_sub, Cubical.mapOne_mapOne, hjC, hjΘ] using hp
  let P : Submodule ℤ (Cubical.OneChain (univ : Set ℂ)) :=
    Finsupp.supported ℤ ℤ {γ | ContDiffOn ℝ 1 (cubicalPath γ).extend I}
  have hC : Cubical.mapOne jC Γ ∈ P :=
    Cubical.mapOne_mem_supported jC Γ _ (by intro γ hγ; exact hΓ γ hγ)
  have hgrid : Cubical.mapOne fullPlaneLift (Cubical.Grid.edgeChain v h w) ∈ P :=
    contDiffOn_cubicalPath_grid_edgeChain v h w
  have hΔ : ∀ γ ∈ Δ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I := by
    have hs : Cubical.mapOne jΘ Δ ∈ P := he' ▸ P.sub_mem hC hgrid
    intro γ hγ
    exact hs ((Cubical.mem_support_mapOne_comp_iff jΘ
      (fun _ _ hab => Subtype.ext (congrArg (fun z : (univ : Set ℂ) => (z : ℂ)) hab)) Δ γ).mpr hγ)
  have hz := cubicalCurveIntegral_eq_zero_of_isNullHomologous hΘ
    (g := fun z => (z - τ)⁻¹) (by
      intro z hz
      exact ((differentiableAt_id.sub_const τ).inv
        (sub_ne_zero.mpr (by intro heq; exact hτ (heq ▸ hz)))).differentiableWithinAt)
    Δ hΔ hnull
  have hi := congrArg (cubicalCurveIntegral (fun z => (z - τ)⁻¹)) he'
  simp only [map_sub, jC, jΘ, cubicalCurveIntegral_mapOne_inclusion, hz] at hi
  exact congrArg ((2 * Real.pi * Complex.I)⁻¹ * ·) (sub_eq_zero.mp hi.symm)

end Complex

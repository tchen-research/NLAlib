import NLAlib.ForMathlib.Topology.RectangularGrid
import NLAlib.ForMathlib.Analysis.Complex.RectangularCellWinding
import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchyFormula

/-! # Actual winding identifies finite rectangular-grid coefficients

The four-edge inverse integrals isolate each cell at its geometric center.
Thus the explicit algebraic filling coefficient equals the actual normalized
native contour integral. No integer winding or filling-support premise is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Finset
open scoped unitInterval
namespace Complex

private theorem curveIntegral_cubicalPath_univ_lift {a b : ℂ} (γ : Path a b)
    (ω : ℂ → ℂ →L[ℂ] ℂ) :
    curveIntegral ω (cubicalPath
      ((⟨fun z => ⟨z, Set.mem_univ z⟩, continuous_id.subtype_mk _⟩ :
        C(ℂ, (Set.univ : Set ℂ))).comp γ.toContinuousMap)) = curveIntegral ω γ := by
  have he : cubicalPath
      ((⟨fun z => ⟨z, Set.mem_univ z⟩, continuous_id.subtype_mk _⟩ :
        C(ℂ, (Set.univ : Set ℂ))).comp γ.toContinuousMap) =
      γ.cast (by simp) (by simp) := by ext t; rfl
  rw [he, curveIntegral_cast]

/-- At a cell center, actual winding of a native finite rectangular grid
cycle equals its explicit integer prefix coefficient. The chain is pushed
through the canonical continuous lift to the full-plane domain subtype.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem cubicalWindingIntegral_rectangularGrid_eq_cellCoefficients
    {m n : ℕ} (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hy : StrictMono y)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (hc : RectangularChain.IsCycle h w) (i : Fin m) (j : Fin n) :
    cubicalWindingIntegral
      (Cubical.mapOne (⟨fun z => ⟨z, Set.mem_univ z⟩,
          continuous_id.subtype_mk _⟩ : C(ℂ, (Set.univ : Set ℂ)))
        (Cubical.Grid.edgeChain (Cubical.RectangularGrid.vertex x y) h w))
      (Cubical.RectangularGrid.center x y i j) =
        ((RectangularChain.cellCoefficients h i j : ℤ) : ℂ) := by
  let v := Cubical.RectangularGrid.vertex x y
  let τ := Cubical.RectangularGrid.center x y i j
  let p : ℂ := 2 * Real.pi * Complex.I
  let L : Cubical.OneChain ℂ →ₗ[ℤ] ℂ :=
    (cubicalCurveIntegral (fun z => (z - τ)⁻¹)).comp
      (Cubical.mapOne (⟨fun z => ⟨z, Set.mem_univ z⟩,
        continuous_id.subtype_mk _⟩ : C(ℂ, (Set.univ : Set ℂ))))
  have hcell (k : Fin m) (l : Fin n) :
      L (Cubical.squareBoundary (Cubical.Grid.cell v k l)) =
        if k = i ∧ l = j then p else 0 := by
    simp only [Cubical.squareBoundary, map_add, map_sub, Cubical.Grid.right_cell,
      Cubical.Grid.left_cell, Cubical.Grid.top_cell, Cubical.Grid.bottom_cell]
    simp only [L, LinearMap.comp_apply, Cubical.mapOne_single, cubicalCurveIntegral,
      Finsupp.linearCombination_single, one_smul]
    simp only [Cubical.Grid.horizontal, Cubical.Grid.vertical,
      curveIntegral_cubicalPath_univ_lift]
    change
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
          (Path.segment (v k.succ l.castSucc) (v k.succ l.succ)) -
        curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
          (Path.segment (v k.castSucc l.castSucc) (v k.castSucc l.succ)) -
        curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
          (Path.segment (v k.castSucc l.succ) (v k.succ l.succ)) +
        curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
          (Path.segment (v k.castSucc l.castSucc) (v k.succ l.castSucc)) = _
    by_cases he : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := he
      rw [if_pos ⟨rfl, rfl⟩]
      obtain ⟨ha, hb, hc', hd⟩ :=
        Cubical.RectangularGrid.center_mem_open_rectangle x y hx hy k l
      have hp := curveIntegral_inv_sub_rectangle_eq_two_pi_I ha hb hc' hd
      change _ = p
      dsimp only [v, Cubical.RectangularGrid.vertex, p, τ]
      linear_combination hp
    · rw [if_neg he]
      have hout := Cubical.RectangularGrid.center_strictly_outside_other_rectangle
        x y hx hy i k j l (by intro hkl; exact he (Prod.mk.inj hkl.symm))
      have hz := curveIntegral_inv_sub_rectangle_eq_zero_of_outside
        (hx.monotone k.castSucc_lt_succ.le) (hy.monotone l.castSucc_lt_succ.le) hout
      dsimp only [v, Cubical.RectangularGrid.vertex]
      linear_combination hz
  have he : L (Cubical.Grid.edgeChain v h w) =
      ((RectangularChain.cellCoefficients h i j : ℤ) : ℂ) * p := by
    rw [← Cubical.Grid.boundaryTwo_cellChain_eq_edgeChain v h w hc]
    simp only [Cubical.Grid.cellChain, map_sum, map_smul, Cubical.boundaryTwo,
      Finsupp.linearCombination_single, one_smul]
    simp only [hcell, smul_ite, smul_zero]
    simp [zsmul_eq_mul, ite_and]
  change p⁻¹ * L (Cubical.Grid.edgeChain v h w) = _
  rw [he]
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  field_simp

end Complex

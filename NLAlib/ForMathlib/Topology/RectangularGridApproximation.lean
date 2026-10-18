import NLAlib.ForMathlib.Topology.RectangularGridLocalFill
import NLAlib.ForMathlib.Topology.CubicalSubdivisionSmall
import NLAlib.ForMathlib.Topology.CubicalGridLinear

/-! # Actual grid approximation of continuous edges

Uniform subdivision and local convex fillings replace each continuous edge
by a finite canonical grid walk. The constructed filling remains in a small
neighborhood of the original trace. The quantizer need not be continuous.
-/

noncomputable section
open Set Metric
open scoped unitInterval
namespace Cubical.RectangularGrid
variable {m n : ℕ} {C : Set ℂ}

/-- The actual integer arrays of the successive grid walks along a uniform
subdivision of an original continuous edge. -/
def subdivisionWalkCoefficients (q : C → Fin (m + 1) × Fin (n + 1))
    (γ : C(I, C)) (k : ℕ) : Grid.Coefficients m n :=
  ∑ i ∈ Finset.range k,
    (Grid.walkHorizontalCoefficients (q (γ (uniformNode k i)))
        (q (γ (uniformNode k (i + 1)))),
      Grid.walkVerticalCoefficients (q (γ (uniformNode k i)))
        (q (γ (uniformNode k (i + 1)))))

/-- Realizing the summed arrays gives exactly the finite sum of the actual
canonical walks between the successive quantized subdivision nodes. -/
theorem edgeChainMap_subdivisionWalkCoefficients
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (γ : C(I, C)) (k : ℕ) :
    Grid.edgeChainMap (vertex x y) (subdivisionWalkCoefficients q γ k) =
      ∑ i ∈ Finset.range k, Grid.walkChain (vertex x y)
        (q (γ (uniformNode k i))) (q (γ (uniformNode k (i + 1)))) := by
  simp only [subdivisionWalkCoefficients, map_sum]
  rfl

/-- The endpoint connectors in a finite sum of actual local comparison
cycles telescope, leaving only the original two endpoint connectors. -/
theorem sum_localComparisonChain_subedge
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (q : C → Fin (m + 1) × Fin (n + 1)) (γ : C(I, C)) {k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.range k,
        localComparisonChain x y q (subedge γ (uniformNode k i) (uniformNode k (i + 1))) =
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ))
          (subdivisionChain γ (uniformNode k) k) +
        Finsupp.single (quantizerConnector x y q (γ 1)) 1 -
        Grid.edgeChainMap (vertex x y) (subdivisionWalkCoefficients q γ k) -
        Finsupp.single (quantizerConnector x y q (γ 0)) 1 := by
  have hzero : uniformNode k 0 = 0 := by
    apply Subtype.ext
    simp [coe_uniformNode_of_le hk (Nat.zero_le k)]
  have hone : uniformNode k k = 1 := by
    apply Subtype.ext
    simp [coe_uniformNode_of_le hk le_rfl, hk.ne']
  rw [edgeChainMap_subdivisionWalkCoefficients]
  simp only [localComparisonChain, subedge_zero, subedge_one, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, subdivisionChain, map_sum, mapOne_single]
  have ht := Finset.sum_range_sub (fun i =>
    Finsupp.single (quantizerConnector x y q (γ (uniformNode k i))) (1 : ℤ)) k
  rw [hone, hzero] at ht
  rw [Finset.sum_sub_distrib] at ht
  rw [(sub_eq_iff_eq_add).mp ht]
  abel

set_option maxHeartbeats 600000 in
/-- An actual sufficiently fine finite grid walk replaces an arbitrary
continuous edge modulo a normalized cubical filling in the prescribed
small neighborhood. Only the final two endpoint connectors remain. -/
theorem exists_isNullHomologous_mapOne_eq_edgeComparison
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x) (hy : Monotone y)
    (q : C → Fin (m + 1) × Fin (n + 1)) {h : ℝ} (hh : 0 < h)
    (hq : ∀ z : C, ‖vertex x y (q z).1 (q z).2 - z‖ < 2 * h)
    (γ : C(I, C)) :
    ∃ c : Grid.Coefficients m n, ∃ Δ : OneChain (thickening (8 * h) C),
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
        C(thickening (8 * h) C, ℂ)) Δ =
          Finsupp.single ((⟨Subtype.val, continuous_subtype_val⟩ : C(C, ℂ)).comp γ) 1 +
            Finsupp.single (quantizerConnector x y q (γ 1)) 1 -
            Grid.edgeChainMap (vertex x y) c -
            Finsupp.single (quantizerConnector x y q (γ 0)) 1 ∧
        IsNullHomologous Δ := by
  classical
  let j : C(C, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨k, hk, hsmall⟩ := exists_uniform_subdivision_image_small (j.comp γ) hh
  have hlocal (i : ℕ) (hi : i < k) :=
    exists_isNullHomologous_mapOne_eq_localComparisonChain_thickening x y hx hy q hh hq
      (subedge γ (uniformNode k i) (uniformNode k (i + 1))) (by
        intro t
        rw [subedge_zero]
        change ‖(γ (Set.Icc.convexComb (uniformNode k i) (uniformNode k (i + 1)) t) : ℂ) -
          γ (uniformNode k i)‖ < h
        exact hsmall i hi t)
  choose Δ hΔ hn using hlocal
  let S : OneChain (thickening (8 * h) C) :=
    ∑ i ∈ Finset.range k, if hi : i < k then Δ i hi else 0
  have hS : IsNullHomologous S := by
    apply isNullHomologous_finsetSum
    intro i hi
    simp only [Finset.mem_range] at hi
    simpa only [dif_pos hi] using hn i hi
  have heS : mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
      C(thickening (8 * h) C, ℂ)) S =
        ∑ i ∈ Finset.range k,
          localComparisonChain x y q (subedge γ (uniformNode k i) (uniformNode k (i + 1))) := by
    simp only [S, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [dif_pos hi]
    exact hΔ i hi
  have hC : C ⊆ thickening (8 * h) C := by
    intro z hz
    exact mem_thickening_iff.mpr ⟨z, hz, by simp; positivity⟩
  let incl : C(C, thickening (8 * h) C) := ContinuousMap.inclusion hC
  let T := mapOne incl (Finsupp.single γ 1 - subdivisionChain γ (uniformNode k) k)
  have hT : IsNullHomologous T :=
    (isNullHomologous_single_sub_uniform_subdivisionChain γ hk).map incl
  have hj : (⟨Subtype.val, continuous_subtype_val⟩ :
      C(thickening (8 * h) C, ℂ)).comp incl = j := by ext z; rfl
  have heT : mapOne (⟨Subtype.val, continuous_subtype_val⟩ :
      C(thickening (8 * h) C, ℂ)) T =
      mapOne j (Finsupp.single γ 1 - subdivisionChain γ (uniformNode k) k) := by
    dsimp only [T]
    rw [mapOne_mapOne, hj]
  refine ⟨subdivisionWalkCoefficients q γ k, T + S, ?_, hT.add hS⟩
  rw [map_add, heS, heT, sum_localComparisonChain_subedge x y q γ hk,
    map_sub, mapOne_single]
  simp only [j]
  abel

end Cubical.RectangularGrid

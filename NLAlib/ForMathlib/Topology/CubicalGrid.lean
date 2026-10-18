import NLAlib.ForMathlib.Topology.CubicalMaps
import NLAlib.ForMathlib.Algebra.RectangularChain
import Mathlib.Analysis.Convex.PathConnected

/-! # Actual continuous fillings of finite vector-space grids

The horizontal and vertical edges are native straight segments. A cell is
the actual bilinear square spanned by its four vertices. Explicit finite
prefix coefficients from `RectangularChain` realize every grid cycle as
the boundary of a finite continuous two-chain.
-/

noncomputable section
open Finset AffineMap
open scoped unitInterval
namespace Cubical.Grid

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {m n : ℕ}

/-- The canonical eastward grid edge. -/
def horizontal (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin (n + 1)) :
    C(I, E) :=
  (Path.segment (v i.castSucc j) (v i.succ j)).toContinuousMap

/-- The canonical northward grid edge. -/
def vertical (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin (m + 1)) (j : Fin n) :
    C(I, E) :=
  (Path.segment (v i j.castSucc) (v i j.succ)).toContinuousMap

/-- The actual bilinear continuous square spanning a grid cell. -/
def cell (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin n) :
    C(I × I, E) :=
  ⟨fun p => lineMap (lineMap (v i.castSucc j.castSucc) (v i.succ j.castSucc) (p.1 : ℝ))
    (lineMap (v i.castSucc j.succ) (v i.succ j.succ) (p.1 : ℝ)) (p.2 : ℝ), by
      simp only [lineMap_apply_module]
      fun_prop⟩

@[simp]
theorem left_cell (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin n) :
    Cubical.left (cell v i j) = vertical v i.castSucc j := by
  ext t
  simp [Cubical.left, cell, vertical, Path.segment_apply]

@[simp]
theorem right_cell (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin n) :
    Cubical.right (cell v i j) = vertical v i.succ j := by
  ext t
  simp [Cubical.right, cell, vertical, Path.segment_apply]

@[simp]
theorem bottom_cell (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin n) :
    Cubical.bottom (cell v i j) = horizontal v i j.castSucc := by
  ext t
  simp [Cubical.bottom, cell, horizontal, Path.segment_apply]

@[simp]
theorem top_cell (v : Fin (m + 1) → Fin (n + 1) → E) (i : Fin m) (j : Fin n) :
    Cubical.top (cell v i j) = horizontal v i j.succ := by
  ext t
  simp [Cubical.top, cell, horizontal, Path.segment_apply]

/-- A finite signed chain of the canonical grid edges. -/
def edgeChain (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ) : OneChain E :=
  (∑ i, ∑ j, h i j • Finsupp.single (horizontal v i j) 1) +
    ∑ i, ∑ j, w i j • Finsupp.single (vertical v i j) 1

/-- The actual finite two-chain with the given cell coefficients. -/
def cellChain (v : Fin (m + 1) → Fin (n + 1) → E)
    (c : Fin m → Fin n → ℤ) : TwoChain E :=
  ∑ i, ∑ j, c i j • Finsupp.single (cell v i j) 1

/-- Only active canonical grid edges contribute to the trace of an actual
grid chain. No condition is required on zero-coefficient grid edges. -/
theorem edgeChain_mapsTo_of_nonzero_edges_mapsTo
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ) (S : Set E)
    (hH : ∀ i j, h i j ≠ 0 → ∀ t, horizontal v i j t ∈ S)
    (hV : ∀ i j, w i j ≠ 0 → ∀ t, vertical v i j t ∈ S) :
    ∀ q ∈ (edgeChain v h w).support, ∀ t, q t ∈ S := by
  classical
  intro q hq t
  by_contra hnot
  have hh (i : Fin m) (j : Fin (n + 1)) :
      (h i j • Finsupp.single (horizontal v i j) (1 : ℤ)) q = 0 := by
    by_cases hc : h i j = 0
    · simp [hc]
    · have hne : horizontal v i j ≠ q := by
        intro he
        exact hnot (he ▸ hH i j hc t)
      simp [hne]
  have hw (i : Fin (m + 1)) (j : Fin n) :
      (w i j • Finsupp.single (vertical v i j) (1 : ℤ)) q = 0 := by
    by_cases hc : w i j = 0
    · simp [hc]
    · have hne : vertical v i j ≠ q := by
        intro he
        exact hnot (he ▸ hV i j hc t)
      simp [hne]
  have hz : edgeChain v h w q = 0 := by
    simp only [edgeChain, Finsupp.add_apply, Finsupp.finsetSum_apply, hh, hw,
      sum_const_zero, zero_add]
  exact (Finsupp.mem_support_iff.mp hq) hz

/-- Explicit prefix coefficients fill an actual grid cycle with actual
continuous bilinear squares. No analytic formula or topological filling is assumed. -/
theorem boundaryTwo_cellChain_eq_edgeChain
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (hc : RectangularChain.IsCycle h w) :
    boundaryTwo (cellChain v (RectangularChain.cellCoefficients h)) = edgeChain v h w := by
  rw [cellChain, map_sum]
  simp only [map_sum, map_smul, boundaryTwo, Finsupp.linearCombination_single, one_smul]
  have he := RectangularChain.sum_edges_eq_sum_cell_boundaries h w hc
    (fun i j => Finsupp.single (horizontal v i j) (1 : ℤ))
    (fun i j => Finsupp.single (vertical v i j) (1 : ℤ))
  rw [edgeChain, he]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [squareBoundary, right_cell, left_cell, top_cell, bottom_cell]
  congr 1
  abel

/-- Every active square of a cell chain comes from a nonzero cell
coefficient. In particular, support containment needs no condition on the
unused grid cells. -/
theorem cellChain_mapsTo_of_nonzero_cell_mapsTo
    (v : Fin (m + 1) → Fin (n + 1) → E) (c : Fin m → Fin n → ℤ) (S : Set E)
    (hS : ∀ i j, c i j ≠ 0 → ∀ t, cell v i j t ∈ S) :
    ∀ q ∈ (cellChain v c).support, ∀ t, q t ∈ S := by
  classical
  intro q hq t
  by_contra hnot
  have hz : cellChain v c q = 0 := by
    simp only [cellChain, Finsupp.finsetSum_apply, Finsupp.smul_apply]
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j _
    by_cases hc : c i j = 0
    · simp [hc]
    · have hne : cell v i j ≠ q := by
        intro he
        exact hnot (he ▸ hS i j hc t)
      simp [hne]
  exact (Finsupp.mem_support_iff.mp hq) hz

/-- The finite endpoint chain of a vertex coefficient array. -/
def vertexChain (v : Fin (m + 1) → Fin (n + 1) → E)
    (a : Fin (m + 1) → Fin (n + 1) → ℤ) : E →₀ ℤ :=
  ∑ i, ∑ j, a i j • Finsupp.single (v i j) 1

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] in
/-- At distinct grid vertices, the vertex-chain coefficient is exactly the
original array entry. -/
theorem vertexChain_apply_vertex
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (hv : Function.Injective (fun p : Fin (m + 1) × Fin (n + 1) => v p.1 p.2))
    (a : Fin (m + 1) → Fin (n + 1) → ℤ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    vertexChain v a (v i j) = a i j := by
  classical
  have he (k : Fin (m + 1)) (l : Fin (n + 1)) : v k l = v i j ↔ k = i ∧ l = j := by
    constructor
    · intro h
      exact Prod.mk.inj (hv h)
    · rintro ⟨rfl, rfl⟩
      rfl
  simp [vertexChain, Finsupp.finsetSum_apply, Finsupp.single_apply, he,
    ite_and]

/-- The native endpoint boundary is the negative finite vertex divergence.
The signs reflect eastward and northward canonical edges. -/
theorem boundaryOne_edgeChain_eq_neg_vertexChain
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ) :
    boundaryOne (edgeChain v h w) =
      -vertexChain v (fun i j => Fin.edgeBoundary h i j + Fin.edgeBoundary (w i) j) := by
  have hh : (∑ i, ∑ j, Fin.edgeBoundary h i j • Finsupp.single (v i j) (1 : ℤ)) =
      ∑ i, ∑ j, h i j •
        (Finsupp.single (v i.castSucc j) 1 - Finsupp.single (v i.succ j) 1) := by
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro j _
    have he (i : Fin (m + 1)) :
        Fin.edgeBoundary h i j = Fin.edgeBoundary (fun k => h k j) i :=
      Fin.map_edgeBoundary (Pi.evalAddMonoidHom (fun _ : Fin (n + 1) => ℤ) j) h i
    simp_rw [he]
    exact Fin.sum_edgeBoundary_smul (fun k => h k j)
      (fun i => Finsupp.single (v i j) (1 : ℤ))
  have hw : (∑ i, ∑ j, Fin.edgeBoundary (w i) j • Finsupp.single (v i j) (1 : ℤ)) =
      ∑ i, ∑ j, w i j •
        (Finsupp.single (v i j.castSucc) 1 - Finsupp.single (v i j.succ) 1) := by
    apply sum_congr rfl
    intro i _
    exact Fin.sum_edgeBoundary_smul (w i) (fun j => Finsupp.single (v i j) (1 : ℤ))
  have hv : vertexChain v (fun i j => Fin.edgeBoundary h i j + Fin.edgeBoundary (w i) j) =
      (∑ i, ∑ j, Fin.edgeBoundary h i j • Finsupp.single (v i j) (1 : ℤ)) +
        ∑ i, ∑ j, Fin.edgeBoundary (w i) j • Finsupp.single (v i j) (1 : ℤ) := by
    simp only [vertexChain, add_smul, sum_add_distrib]
  rw [hv, hh, hw]
  simp only [edgeChain, map_add, map_sum, map_smul, boundaryOne,
    Finsupp.linearCombination_single, one_smul, horizontal, vertical, Path.coe_toContinuousMap,
    Path.source, Path.target]
  simp only [smul_sub, sum_sub_distrib]
  abel

/-- Native endpoint closure of an actual grid chain gives the finite
coefficient conservation law, provided the grid vertices are distinct. -/
theorem isCycle_of_boundaryOne_edgeChain_eq_zero
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (hv : Function.Injective (fun p : Fin (m + 1) × Fin (n + 1) => v p.1 p.2))
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (hc : boundaryOne (edgeChain v h w) = 0) : RectangularChain.IsCycle h w := by
  rw [boundaryOne_edgeChain_eq_neg_vertexChain, neg_eq_zero] at hc
  intro i j
  have he := congrArg (fun c : E →₀ ℤ => c (v i j)) hc
  simpa only [vertexChain_apply_vertex v hv, Finsupp.zero_apply] using he

/-- If all cells with nonzero explicit prefix coefficient lie in a domain,
the actual grid cycle has an actual finite cubical filling in that domain.
No assumption is imposed on any unused cell, and no Cauchy formula is a premise. -/
theorem exists_isNullHomologous_mapOne_eq_edgeChain
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (hc : RectangularChain.IsCycle h w) (S : Set E)
    (hS : ∀ i j, RectangularChain.cellCoefficients h i j ≠ 0 →
      ∀ t, cell v i j t ∈ S) :
    ∃ Γ : OneChain S,
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(S, E)) Γ = edgeChain v h w ∧
        IsNullHomologous Γ := by
  obtain ⟨T, hT⟩ := exists_mapTwo_subtype_val_eq
    (cellChain v (RectangularChain.cellCoefficients h)) S
    (cellChain_mapsTo_of_nonzero_cell_mapsTo v _ S hS)
  refine ⟨boundaryTwo T, ?_, ⟨T, 0, by simp⟩⟩
  rw [← boundaryTwo_mapTwo, hT, boundaryTwo_cellChain_eq_edgeChain v h w hc]

end Cubical.Grid

import NLAlib.ForMathlib.Analysis.Complex.PrimitiveTransport
import NLAlib.ForMathlib.Algebra.FiniteGridBoundary

/-! # Continuous homotopy grids with local primitive charts

Actual local primitives on the closed cells of a finite grid make shared
edge increments equal, even for a merely continuous homotopy. Finite algebra
then cancels the interior edges. The grid is constructed from holomorphy and
compactness, without a C² homotopy or assumed Cauchy formula.

The finite-grid construction is ported from the local deferred Jordan-contour
development of 2026-10-14, independently of its fixed-endpoint path theory.
-/

noncomputable section
open Set Finset Metric
open scoped unitInterval
namespace Complex

/-- An actual finite primitive chart grid for a continuous square map.
Each chart contains the image of its entire closed cell. -/
structure PrimitiveHomotopyGrid (g : ℂ → ℂ) (ψ : ℝ × ℝ → ℂ) where
  size : ℕ
  size_pos : 0 < size
  chart : ℕ → ℕ → Set ℂ
  primitive : ℕ → ℕ → ℂ → ℂ
  isOpen_chart : ∀ i < size, ∀ j < size, IsOpen (chart i j)
  hasDerivAt_primitive : ∀ i < size, ∀ j < size, ∀ z ∈ chart i j,
    HasDerivAt (primitive i j) (g z) z
  continuousOn : ∀ i < size, ∀ j < size, ContinuousOn g (chart i j)
  mapsTo_chart : ∀ i < size, ∀ j < size,
    ∀ t ∈ Icc (((i : ℝ) / size), ((j : ℝ) / size))
      (((i + 1 : ℝ) / size), ((j + 1 : ℝ) / size)), ψ t ∈ chart i j

namespace PrimitiveHomotopyGrid

/-- The bottom edge increment of the actual primitive in a cell. -/
def bottom {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : ℂ := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j : ℝ) / D.size)))

/-- The top edge increment of the actual primitive in a cell. -/
def top {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : ℂ := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j + 1 : ℝ) / D.size)))

/-- The left edge increment of the actual primitive in a cell. -/
def left {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : ℂ := D.primitive i j (ψ (((i : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j : ℝ) / D.size)))

/-- The right edge increment of the actual primitive in a cell. -/
def right {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : ℂ := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j : ℝ) / D.size)))

private theorem node_le_next {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (i : ℕ) :
    (i : ℝ) / D.size ≤ (i + 1 : ℝ) / D.size :=
  div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg D.size)

/-- Two adjacent horizontal edges agree because their different primitives
have the same derivative along the actual continuous shared edge. -/
theorem bottom_succ_eq_top {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) {i j : ℕ}
    (hi : i < D.size) (hj : j + 1 < D.size) : D.bottom i (j + 1) = D.top i j := by
  have h := sub_eq_sub_of_hasDerivAt_of_continuous
    (γ := fun t => ψ (t, ((j + 1 : ℝ) / D.size)))
    (hψ.comp (continuous_id.prodMk continuous_const)) (D.node_le_next i)
    (D.isOpen_chart i hi (j + 1) hj) (D.isOpen_chart i hi j (by omega))
    (D.hasDerivAt_primitive i hi (j + 1) hj) (D.hasDerivAt_primitive i hi j (by omega))
    (fun t ht => D.mapsTo_chart i hi (j + 1) hj (t, ((j + 1 : ℝ) / D.size))
      ⟨⟨ht.1, by simp⟩, ⟨ht.2, by simpa only [Nat.cast_add, Nat.cast_one] using D.node_le_next (j + 1)⟩⟩)
    (fun t ht => D.mapsTo_chart i hi j (by omega) (t, ((j + 1 : ℝ) / D.size))
      ⟨⟨ht.1, D.node_le_next j⟩, ⟨ht.2, le_rfl⟩⟩)
  simpa only [bottom, top, Nat.cast_add, Nat.cast_one] using h

/-- Two adjacent vertical edges agree for the same continuous-path primitive
reason, without any differentiability of the square map. -/
theorem left_succ_eq_right {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) {i j : ℕ}
    (hi : i + 1 < D.size) (hj : j < D.size) : D.left (i + 1) j = D.right i j := by
  have h := sub_eq_sub_of_hasDerivAt_of_continuous
    (γ := fun t => ψ (((i + 1 : ℝ) / D.size), t))
    (hψ.comp (continuous_const.prodMk continuous_id)) (D.node_le_next j)
    (D.isOpen_chart (i + 1) hi j hj) (D.isOpen_chart i (by omega) j hj)
    (D.hasDerivAt_primitive (i + 1) hi j hj) (D.hasDerivAt_primitive i (by omega) j hj)
    (fun t ht => D.mapsTo_chart (i + 1) hi j hj (((i + 1 : ℝ) / D.size), t)
      ⟨⟨by simp, ht.1⟩, ⟨by simpa only [Nat.cast_add, Nat.cast_one] using D.node_le_next (i + 1), ht.2⟩⟩)
    (fun t ht => D.mapsTo_chart i (by omega) j hj (((i + 1 : ℝ) / D.size), t)
      ⟨⟨D.node_le_next i, ht.1⟩, ⟨le_rfl, ht.2⟩⟩)
  simpa only [left, right, Nat.cast_add, Nat.cast_one] using h

/-- All actual interior edge increments cancel, leaving precisely the outer
boundary transport of a continuous primitive-charted square. -/
theorem sum_right_sub_sum_left_eq_sum_top_sub_sum_bottom
    {g : ℂ → ℂ} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) :
    (∑ j ∈ range D.size, D.right (D.size - 1) j) - (∑ j ∈ range D.size, D.left 0 j) =
      (∑ i ∈ range D.size, D.top i (D.size - 1)) - (∑ i ∈ range D.size, D.bottom i 0) := by
  apply sum_grid_boundary_eq _ _ _ _ D.size_pos
  · intro i _ j _
    dsimp [bottom, top, left, right]
    ring
  · exact fun _ hi _ hj => D.bottom_succ_eq_top hψ hi hj
  · exact fun _ hi _ hj => D.left_succ_eq_right hψ hi hj

end PrimitiveHomotopyGrid

/-- Every compact continuous square inside an open holomorphy domain has an
actual finite primitive grid. Its mesh and primitives are derived by compact
Lebesgue subdivision and local convex primitives. -/
theorem nonempty_primitiveHomotopyGrid_of_differentiableOn
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hψΩ : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ Ω) :
    Nonempty (PrimitiveHomotopyGrid g ψ) := by
  classical
  have hrad : ∀ z : Ω, ∃ r : ℝ, 0 < r ∧ ball (z : ℂ) r ⊆ Ω :=
    fun z => mem_nhds_iff.mp (hΩ.mem_nhds z.property)
  choose r hr hball using hrad
  let B : Ω → Set ℂ := fun z => ball (z : ℂ) (r z)
  have hprimitive : ∀ z : Ω, ∃ G : ℂ → ℂ, ∀ w ∈ B z, HasDerivAt G (g w) w := by
    intro z
    obtain ⟨G, hG⟩ := (convex_ball (z : ℂ) (r z)).exists_forall_hasDerivWithinAt
      (hg.mono (hball z))
    exact ⟨G, fun w hw => (hG w hw).hasDerivAt (isOpen_ball.mem_nhds hw)⟩
  choose G hG using hprimitive
  have hcover : ψ '' Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ z : Ω, B z := by
    rintro z ⟨t, ht, rfl⟩
    apply mem_iUnion.mpr
    exact ⟨⟨ψ t, hψΩ t ht⟩, mem_ball_self (hr _)⟩
  obtain ⟨n, hn, hmesh⟩ := exists_uniform_grid_subordinate_open_cover ψ hψ B
    (fun _ => isOpen_ball) hcover
  choose J hJ using hmesh
  let K : ℕ → ℕ → Ω := fun i j =>
    if hi : i < n then if hj : j < n then J i hi j hj else J 0 hn 0 hn else J 0 hn 0 hn
  refine ⟨⟨n, hn, fun i j => B (K i j), fun i j => G (K i j),
    fun _ _ _ _ => isOpen_ball, fun i _ j _ => hG (K i j),
    fun i _ j _ => hg.continuousOn.mono (hball (K i j)), ?_⟩⟩
  intro i hi j hj
  simpa only [K, dif_pos hi, dif_pos hj] using hJ i hi j hj

end Complex

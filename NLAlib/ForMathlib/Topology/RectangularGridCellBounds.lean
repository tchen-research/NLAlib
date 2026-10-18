import NLAlib.ForMathlib.Topology.RectangularGrid
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith

/-! # Distance control within actual rectangular grid cells

Both coordinate widths bound the distance to the actual cell center. The
result is independent of any quantizer or analytic winding construction.
-/

noncomputable section
open Set
open scoped unitInterval
namespace Cubical.RectangularGrid

/-- If each coordinate width is at most `h`, every point of the actual
closed cell lies within `h` of its geometric center. -/
theorem norm_cell_sub_center_le {m n : ℕ}
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hy : Monotone y) (i : Fin m) (j : Fin n) {h : ℝ}
    (hwidth : x i.succ - x i.castSucc ≤ h) (hheight : y j.succ - y j.castSucc ≤ h)
    (p : I × I) : ‖Grid.cell (vertex x y) i j p - center x y i j‖ ≤ h := by
  obtain ⟨hre, him⟩ := cell_mem_rectangle x y hx hy i j p
  have hr : |(Grid.cell (vertex x y) i j p - center x y i j).re| ≤ h / 2 := by
    rw [Complex.sub_re, center_re, abs_le]
    constructor <;> linarith [hre.1, hre.2]
  have hi : |(Grid.cell (vertex x y) i j p - center x y i j).im| ≤ h / 2 := by
    rw [Complex.sub_im, center_im, abs_le]
    constructor <;> linarith [him.1, him.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- Any two points of the same actual closed cell are within twice the
common coordinate-width bound. -/
theorem norm_cell_sub_cell_le {m n : ℕ}
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hy : Monotone y) (i : Fin m) (j : Fin n) {h : ℝ}
    (hwidth : x i.succ - x i.castSucc ≤ h) (hheight : y j.succ - y j.castSucc ≤ h)
    (p q : I × I) : ‖Grid.cell (vertex x y) i j p - Grid.cell (vertex x y) i j q‖ ≤ 2 * h := by
  have hp := norm_cell_sub_center_le x y hx hy i j hwidth hheight p
  have hq := norm_cell_sub_center_le x y hx hy i j hwidth hheight q
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (Grid.cell (vertex x y) i j p) (center x y i j) (Grid.cell (vertex x y) i j q)
  rw [norm_sub_rev (center x y i j)] at ht
  linarith

end Cubical.RectangularGrid

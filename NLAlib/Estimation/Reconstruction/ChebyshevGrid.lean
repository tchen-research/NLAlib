import NLAlib.Polynomial.Chebyshev.Core
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Angular quantization on a Chebyshev grid

The cells are uniform in angle, not in the original coordinate. Clipping the
floor at the last cell handles the endpoint `x = -1` without an exceptional atom.
Source: Musco--Musco--Rosenblatt--Singh, Corollary 2 and Appendix C.
-/

noncomputable section
open MeasureTheory Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The midpoint angle of the `i`th of `g` equal angular cells. -/
def chebyshevGridAngle (g : ℕ) (i : Fin g) : ℝ :=
  (2 * (i : ℕ) + 1) * Real.pi / (2 * g)

/-- Measurable nearest-midpoint angular assignment, with the last endpoint clipped. -/
def chebyshevGridIndex (g : ℕ) (hg : 0 < g) (x : ℝ) : Fin g :=
  ⟨min ⌊(g : ℝ) * Real.arccos x / Real.pi⌋₊ (g - 1),
    lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

/-- The grid assignment is measurable, including both interval endpoints. -/
theorem measurable_chebyshevGridIndex (g : ℕ) (hg : 0 < g) :
    Measurable (chebyshevGridIndex g hg) := by
  have hm : Measurable (fun x => min ⌊(g : ℝ) * Real.arccos x / Real.pi⌋₊ (g - 1)) :=
    (Nat.measurable_floor.comp
      ((Real.continuous_arccos.measurable.const_mul (g : ℝ)).div_const Real.pi)).min measurable_const
  have he : MeasurableEmbedding (Fin.val : Fin g → ℕ) :=
    ⟨Fin.val_injective, measurable_of_finite _, fun s _ => (Set.to_countable _).measurableSet⟩
  exact he.measurable_comp_iff.mp hm

/-- The selected grid midpoint is within half an angular cell. -/
theorem abs_arccos_sub_chebyshevGridAngle_le (g : ℕ) (hg : 0 < g) (x : ℝ) :
    |Real.arccos x - chebyshevGridAngle g (chebyshevGridIndex g hg x)| ≤ Real.pi / (2 * g) := by
  let y : ℝ := (g : ℝ) * Real.arccos x / Real.pi
  have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.arccos_nonneg x))
    Real.pi_pos.le
  have hyg : y ≤ g := by
    apply (div_le_iff₀ Real.pi_pos).2
    exact mul_le_mul_of_nonneg_left (Real.arccos_le_pi x) (Nat.cast_nonneg _)
  have hf := Nat.floor_le hy0
  have hfu := Nat.lt_floor_add_one y
  let i : ℕ := min ⌊y⌋₊ (g - 1)
  have hil : (i : ℝ) ≤ y := (Nat.cast_le.mpr (Nat.min_le_left _ _)).trans hf
  have hiu : y ≤ (i : ℝ) + 1 := by
    by_cases h : ⌊y⌋₊ ≤ g - 1
    · simpa only [i, min_eq_left h] using hfu.le
    · have he : i = g - 1 := min_eq_right (by omega)
      have hg' : ((g - 1 : ℕ) : ℝ) + 1 = g := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ g))
      simpa only [he, hg'] using hyg
  have hgpos : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hscale : Real.arccos x - chebyshevGridAngle g (chebyshevGridIndex g hg x) =
      (y - ((i : ℝ) + 1 / 2)) * (Real.pi / g) := by
    simp only [chebyshevGridAngle, chebyshevGridIndex]
    change Real.arccos x - (2 * (i : ℝ) + 1) * Real.pi / (2 * g) = _
    dsimp [y]
    field_simp
  rw [hscale, abs_mul, abs_of_pos (div_pos Real.pi_pos hgpos)]
  have hi : |y - ((i : ℝ) + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ (1 / 2) * (Real.pi / g) := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = _ := by ring

/-- Angular quantization controls degree-`j` Chebyshev values by `j` times
half the angular cell width; it avoids the quadratic endpoint derivative bound. -/
theorem abs_eval_chebyshev_sub_grid_le (g : ℕ) (hg : 0 < g) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (j : ℕ) :
    |(T ℝ (j : ℤ)).eval x - (T ℝ (j : ℤ)).eval (chebyshevZero g (chebyshevGridIndex g hg x))| ≤
      j * Real.pi / (2 * g) := by
  have hcos := Real.abs_cos_sub_cos_le
    ((j : ℝ) * Real.arccos x) ((j : ℝ) * chebyshevGridAngle g (chebyshevGridIndex g hg x))
  have hT : (T ℝ (j : ℤ)).eval x = Real.cos ((j : ℝ) * Real.arccos x) := by
    calc
      _ = (T ℝ (j : ℤ)).eval (Real.cos (Real.arccos x)) := by rw [Real.cos_arccos hx.1 hx.2]
      _ = _ := by simp [T_real_cos]
  have hTgrid : (T ℝ (j : ℤ)).eval (chebyshevZero g (chebyshevGridIndex g hg x)) =
      Real.cos ((j : ℝ) * chebyshevGridAngle g (chebyshevGridIndex g hg x)) := by
    rw [chebyshevZero, T_real_cos]
    simp only [Int.cast_natCast, chebyshevGridAngle]
  rw [hT, hTgrid]
  calc
    _ ≤ |(j : ℝ) * Real.arccos x - (j : ℝ) *
        chebyshevGridAngle g (chebyshevGridIndex g hg x)| := hcos
    _ = (j : ℝ) * |Real.arccos x - chebyshevGridAngle g (chebyshevGridIndex g hg x)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
    _ ≤ (j : ℝ) * (Real.pi / (2 * g)) :=
      mul_le_mul_of_nonneg_left (abs_arccos_sub_chebyshevGridAngle_le g hg x) (Nat.cast_nonneg j)
    _ = _ := by ring

end NLAlib

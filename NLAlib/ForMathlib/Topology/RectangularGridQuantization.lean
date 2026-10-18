import NLAlib.ForMathlib.Topology.RectangularGrid
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Arbitrarily fine finite rectangular grids near a compact trace

The finite quantizer is constructed by actual integer floors. Every point
of the compact set has a grid vertex at distance less than twice the chosen
mesh width. No continuity of this necessarily discontinuous quantizer is
asserted or needed for the local contour filling construction.
-/

noncomputable section
open Set Bornology
namespace Cubical.RectangularGrid

/-- The uniform coordinate array centered at zero, with `2N+1` vertices. -/
def coordinate (N : ℕ) (h : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ((i : ℝ) - N) * h

/-- A positive mesh gives strictly ordered, distinct grid coordinates. -/
theorem strictMono_coordinate (N : ℕ) {h : ℝ} (hh : 0 < h) :
    StrictMono (coordinate N h) := by
  intro i j hij
  exact mul_lt_mul_of_pos_right (sub_lt_sub_right (by exact_mod_cast hij) _) hh

/-- The actual spacing between adjacent coordinates is exactly the mesh width. -/
theorem coordinate_succ_sub_castSucc (N : ℕ) (h : ℝ) (i : Fin (2 * N)) :
    coordinate N h i.succ - coordinate N h i.castSucc = h := by
  simp only [coordinate, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- The finite index of an integer floor lying in the specified coordinate box. -/
def floorIndex (N : ℕ) (u : ℝ) (hlo : -(N : ℝ) ≤ u) (hhi : u < N) : Fin (2 * N + 1) :=
  ⟨(⌊u⌋ + (N : ℤ)).toNat, by
    have hl : -(N : ℤ) ≤ ⌊u⌋ := Int.le_floor.mpr (by exact_mod_cast hlo)
    have hh : ⌊u⌋ < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hhi)
    omega⟩

/-- The finite index retains the actual integer-floor coordinate. -/
theorem coe_floorIndex (N : ℕ) (u : ℝ) (hlo : -(N : ℝ) ≤ u) (hhi : u < N) :
    (floorIndex N u hlo hhi : ℝ) = (⌊u⌋ : ℝ) + N := by
  have hl : -(N : ℤ) ≤ ⌊u⌋ := Int.le_floor.mpr (by exact_mod_cast hlo)
  have hn : 0 ≤ ⌊u⌋ + (N : ℤ) := by omega
  have he := Int.toNat_of_nonneg hn
  change (((⌊u⌋ + (N : ℤ)).toNat : ℕ) : ℝ) = _
  exact_mod_cast he

/-- The quantized coordinate lies below the original coordinate and differs
from it by strictly less than one actual mesh width. -/
theorem coordinate_floorIndex_error (N : ℕ) {h : ℝ} (hh : 0 < h) (r : ℝ)
    (hlo : -(N : ℝ) ≤ r / h) (hhi : r / h < N) :
    coordinate N h (floorIndex N (r / h) hlo hhi) ≤ r ∧
      r - coordinate N h (floorIndex N (r / h) hlo hhi) < h := by
  have he : coordinate N h (floorIndex N (r / h) hlo hhi) = (⌊r / h⌋ : ℝ) * h := by
    rw [coordinate, coe_floorIndex]
    ring
  rw [he]
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le _)
  · have hf := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (r / h))
    nlinarith

/-- A compact planar trace fits strictly inside some finite normalized
integer grid box for every positive mesh width. -/
theorem exists_normalized_coordinate_box {C : Set ℂ} (hC : IsCompact C)
    {h : ℝ} (hh : 0 < h) :
    ∃ N : ℕ, ∀ z ∈ C,
      (-(N : ℝ) ≤ z.re / h ∧ z.re / h < N) ∧
        (-(N : ℝ) ≤ z.im / h ∧ z.im / h < N) := by
  obtain ⟨R, hRpos, hR⟩ := hC.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (R / h + 1)
  refine ⟨N, ?_⟩
  intro z hz
  have hnorm := hR z hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hNr : R / h < (N : ℝ) := by linarith
  have hpos : 0 < (N : ℝ) := by linarith [div_pos hRpos hh]
  have hr : -R ≤ z.re ∧ z.re ≤ R := by
    constructor <;> linarith [le_abs_self z.re, neg_le_abs z.re]
  have hi : -R ≤ z.im ∧ z.im ≤ R := by
    constructor <;> linarith [le_abs_self z.im, neg_le_abs z.im]
  constructor
  · constructor
    · have hd := (div_le_div_iff_of_pos_right hh).mpr hr.1
      rw [neg_div] at hd
      linarith
    · exact ((div_le_div_iff_of_pos_right hh).mpr hr.2).trans_lt hNr
  · constructor
    · have hd := (div_le_div_iff_of_pos_right hh).mpr hi.1
      rw [neg_div] at hd
      linarith
    · exact ((div_le_div_iff_of_pos_right hh).mpr hi.2).trans_lt hNr

/-- An actual finite grid and a specified floor quantizer approximate every
point of a compact planar trace by less than two mesh widths. -/
theorem exists_quantizer {C : Set ℂ} (hC : IsCompact C) {h : ℝ} (hh : 0 < h) :
    ∃ N : ℕ, ∃ q : C → Fin (2 * N + 1) × Fin (2 * N + 1),
      ∀ z : C, ‖vertex (coordinate N h) (coordinate N h) (q z).1 (q z).2 - z‖ < 2 * h := by
  obtain ⟨N, hN⟩ := exists_normalized_coordinate_box hC hh
  let q : C → Fin (2 * N + 1) × Fin (2 * N + 1) := fun z =>
    (floorIndex N (z.val.re / h) (hN z z.property).1.1 (hN z z.property).1.2,
      floorIndex N (z.val.im / h) (hN z z.property).2.1 (hN z z.property).2.2)
  refine ⟨N, q, ?_⟩
  intro z
  have hre := coordinate_floorIndex_error N hh z.val.re (hN z z.property).1.1 (hN z z.property).1.2
  have him := coordinate_floorIndex_error N hh z.val.im (hN z z.property).2.1 (hN z z.property).2.2
  apply (Complex.norm_le_abs_re_add_abs_im _).trans_lt
  simp only [Complex.sub_re, Complex.sub_im, vertex_re, vertex_im]
  change |coordinate N h (q z).1 - z.val.re| + |coordinate N h (q z).2 - z.val.im| < 2 * h
  rw [abs_of_nonpos (sub_nonpos.mpr hre.1), abs_of_nonpos (sub_nonpos.mpr him.1)]
  linarith [hre.2, him.2]

end Cubical.RectangularGrid

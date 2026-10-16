import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.RCLike.Basic

/-! # Conformally labelled block-diagonal matrices -/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Entries vanish when their row and column belong to distinct labelled blocks. -/
def ConformalBlockDiagonal {K m n ι : Type*} [Zero K] (A : Matrix m n K)
    (row : m → ι) (col : n → ι) : Prop := ∀ i j, row i ≠ col j → A i j = 0

namespace ConformalBlockDiagonal
variable {K m n p ι : Type*} [RCLike K] {row : m → ι} {mid : n → ι} {col : p → ι}

/-- Products retain conformal block diagonality. -/
theorem mul [Fintype n] {A : Matrix m n K} {B : Matrix n p K}
    (hA : ConformalBlockDiagonal A row mid) (hB : ConformalBlockDiagonal B mid col) :
    ConformalBlockDiagonal (A * B) row col := by
  classical
  intro i j hij
  apply Finset.sum_eq_zero
  intro t _
  change A i t * B t j = 0
  by_cases hit : row i = mid t
  · rw [hB t j (by simpa [← hit] using hij), mul_zero]
  · rw [hA i t hit, zero_mul]

/-- Adjointing exchanges the row and column block labels. -/
theorem conjTranspose {A : Matrix m n K} (hA : ConformalBlockDiagonal A row mid) :
    ConformalBlockDiagonal Aᴴ mid row := by
  intro i j hij
  simp [Matrix.conjTranspose_apply, hA j i hij.symm]

/-- Differences retain conformal block diagonality. -/
theorem sub {A B : Matrix m n K} (hA : ConformalBlockDiagonal A row mid)
    (hB : ConformalBlockDiagonal B row mid) : ConformalBlockDiagonal (A - B) row mid := by
  intro i j hij
  simp [hA i j hij, hB i j hij]

/-- An invertible block-diagonal matrix has a block-diagonal inverse; no
principal-block invertibility assumptions are added to the statement. -/
theorem inv [Fintype m] [DecidableEq m] [LinearOrder ι] {A : Matrix m m K}
    (hA : ConformalBlockDiagonal A row row) (hunit : IsUnit A.det) :
    ConformalBlockDiagonal A⁻¹ row row := by
  let : Invertible A := ((Matrix.isUnit_iff_isUnit_det A).mpr hunit).invertible
  have hu : Matrix.BlockTriangular A row := fun i j h => hA i j (ne_of_gt h)
  have hd : Matrix.BlockTriangular A (fun i => OrderDual.toDual (row i)) :=
    fun i j h => hA i j (ne_of_lt h)
  have hui := Matrix.blockTriangular_inv_of_blockTriangular hu
  have hdi := Matrix.blockTriangular_inv_of_blockTriangular hd
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hdi h
  · exact hui h

end ConformalBlockDiagonal
end NLAlib

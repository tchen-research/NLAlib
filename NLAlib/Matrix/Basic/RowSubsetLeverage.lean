import NLAlib.Matrix.Basic.RowSubsetGram
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Spectral.RankOneEigenvalue

/-! # Leverage scores for reverse row deletion

Removing one row has determinant ratio `1-h_i`, and the full-column-rank
leverage scores sum to the column dimension. The formulas use ordinary
inverses only on supported nonsingular Gram matrices.
Source: Dereziński–Warmuth 2018, Theorem 2.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- The row leverage score relative to the selected ambient rows. Its
ordinary-inverse formula is used with nonsingular restricted Gram matrices. -/
def rowSubsetLeverage (X : Matrix n d 𝕜) (T : Finset n) (i : n) : ℝ :=
  RCLike.re (quadForm (rowSubsetGram X T)⁻¹ (star (X i)))

/-- Every row leverage score is nonnegative on a Gram matrix.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem rowSubsetLeverage_nonneg (X : Matrix n d 𝕜) (T : Finset n) (i : n) :
    0 ≤ rowSubsetLeverage X T i :=
  (rowSubsetGram_posSemidef X T).inv.re_quadForm_nonneg _

/-- The determinant after removing a row is the original determinant times
one minus its leverage. Singular destinations are included.
Dereziński–Warmuth 2018, Theorem 2. -/
theorem rowSubsetVolume_erase_eq (X : Matrix n d 𝕜) (T : Finset n) {i : n}
    (hi : i ∈ T) (hT : 0 < rowSubsetVolume X T) :
    rowSubsetVolume X (T.erase i) = rowSubsetVolume X T * (1 - rowSubsetLeverage X T i) := by
  have hG := (rowSubsetVolume_pos_iff_isUnit X T).mp hT
  have hdet := det_add_vecMulVec ((Matrix.isUnit_iff_isUnit_det _).mp hG)
    (-(star (X i))) (X i)
  have hd : (rowSubsetGram X (T.erase i)).det = (rowSubsetGram X T).det *
      (1 - quadForm (rowSubsetGram X T)⁻¹ (star (X i))) := by
    rw [rowSubsetGram_erase X T hi]
    simpa only [Matrix.neg_vecMulVec, ← sub_eq_add_neg, Matrix.mulVec_neg,
      dotProduct_neg, quadForm, star_star] using hdet
  unfold rowSubsetVolume rowSubsetLeverage
  rw [hd, ← ofReal_rowSubsetVolume X T, RCLike.re_ofReal_mul, map_sub, RCLike.one_re,
    RCLike.ofReal_re]

/-- A selected row has leverage at most one, including rank-destroying
deletions for which its leverage is exactly one.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem rowSubsetLeverage_le_one (X : Matrix n d 𝕜) (T : Finset n) {i : n}
    (hi : i ∈ T) (hT : 0 < rowSubsetVolume X T) : rowSubsetLeverage X T i ≤ 1 := by
  have h := rowSubsetVolume_nonneg X (T.erase i)
  rw [rowSubsetVolume_erase_eq X T hi hT] at h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hT).mp h)

/-- Full-rank leverage scores over the selected rows sum to the number of
columns. Dereziński–Warmuth 2018, proof of Theorem 2.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem sum_rowSubsetLeverage (X : Matrix n d 𝕜) (T : Finset n)
    (hT : 0 < rowSubsetVolume X T) :
    (∑ i ∈ T, rowSubsetLeverage X T i) = Fintype.card d := by
  have hG := (rowSubsetVolume_pos_iff_isUnit X T).mp hT
  have ht : ∑ i ∈ T, quadForm (rowSubsetGram X T)⁻¹ (star (X i)) =
      ((rowSubsetGram X T)⁻¹ * rowSubsetGram X T).trace := by
    rw [rowSubsetGram_eq_sum, Finset.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    simp only [quadForm, star_star]
    exact dotProduct_comm _ _
  simp only [rowSubsetLeverage, ← map_sum]
  rw [ht, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hG),
    Matrix.trace_one, RCLike.natCast_re]

end NLAlib

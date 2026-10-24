import NLAlib.Matrix.Basic.CoordinateSelector
import NLAlib.Matrix.Basic.CauchyBinetAdjoint
import NLAlib.ForMathlib.Combinatorics.SubsetSums
import Mathlib.Analysis.Matrix.PosDef

/-! # Gram determinants of padded row restrictions

Cauchy–Binet and finite superset counting give the row-volume normalizer
without any rank assumption. Invertibility is needed only for its positivity.
Source: Dereziński–Warmuth 2018, Theorem 2.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- The column Gram matrix of the rows in `S`, padded with zero rows on its
complement. The ambient row labels are retained. -/
def rowSubsetGram (X : Matrix n d 𝕜) (S : Finset n) : Matrix d d 𝕜 :=
  Xᴴ * (coordinateSelector S : Matrix n n 𝕜) * X

omit [Fintype d] [DecidableEq d] in
/-- Padded row restriction has the same Gram matrix as literal restriction. -/
theorem rowSubsetGram_eq_conjTranspose_mul_self (X : Matrix n d 𝕜) (S : Finset n) :
    rowSubsetGram X S = ((coordinateSelector S : Matrix n n 𝕜) * X)ᴴ *
      ((coordinateSelector S : Matrix n n 𝕜) * X) := by
  simp only [rowSubsetGram, Matrix.conjTranspose_mul,
    (coordinateSelector_isHermitian (𝕜 := 𝕜) S).eq, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Xᴴ ((coordinateSelector S : Matrix n n 𝕜)) ((coordinateSelector S : Matrix n n 𝕜)),
    coordinateSelector_mul_self]

omit [DecidableEq d] in
/-- Every row-subset Gram matrix is positive semidefinite, including
singular and empty restrictions. -/
theorem rowSubsetGram_posSemidef (X : Matrix n d 𝕜) (S : Finset n) :
    (rowSubsetGram X S).PosSemidef := by
  rw [rowSubsetGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

set_option backward.isDefEq.respectTransparency false in
omit [Fintype d] [DecidableEq d] in
/-- A row-subset Gram matrix is the sum of the selected row outer products. -/
theorem rowSubsetGram_eq_sum (X : Matrix n d 𝕜) (S : Finset n) :
    rowSubsetGram X S = ∑ i ∈ S, Matrix.vecMulVec (star (X i)) (X i) := by
  classical
  ext a b
  rw [rowSubsetGram, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [coordinateSelector_mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- Removing a row subtracts precisely its rank-one Gram contribution. -/
theorem rowSubsetGram_erase (X : Matrix n d 𝕜) (T : Finset n) {i : n} (hi : i ∈ T) :
    rowSubsetGram X (T.erase i) = rowSubsetGram X T - Matrix.vecMulVec (star (X i)) (X i) := by
  rw [rowSubsetGram_eq_sum, rowSubsetGram_eq_sum, eq_sub_iff_add_eq]
  exact Finset.sum_erase_add _ _ hi

/-- The row-subset determinant is real and nonnegative. -/
def rowSubsetVolume (X : Matrix n d 𝕜) (S : Finset n) : ℝ :=
  RCLike.re (rowSubsetGram X S).det

/-- Every row-volume weight is nonnegative. -/
theorem rowSubsetVolume_nonneg (X : Matrix n d 𝕜) (S : Finset n) :
    0 ≤ rowSubsetVolume X S :=
  (RCLike.nonneg_iff.mp (rowSubsetGram_posSemidef X S).det_nonneg).1

/-- The determinant of a Gram matrix equals the scalar embedding of its
row-volume weight. -/
theorem ofReal_rowSubsetVolume (X : Matrix n d 𝕜) (S : Finset n) :
    (rowSubsetVolume X S : 𝕜) = (rowSubsetGram X S).det := by
  exact RCLike.ext (by simp [rowSubsetVolume])
    (by simpa using (RCLike.nonneg_iff.mp (rowSubsetGram_posSemidef X S).det_nonneg).2.symm)

/-- Positive row volume is exactly nonsingularity of the restricted column
Gram matrix, so it is the usual full-column-rank support condition. -/
theorem rowSubsetVolume_pos_iff_isUnit (X : Matrix n d 𝕜) (S : Finset n) :
    0 < rowSubsetVolume X S ↔ IsUnit (rowSubsetGram X S) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← ofReal_rowSubsetVolume]
  constructor
  · intro h hzero
    have hz := congrArg RCLike.re hzero
    simp only [RCLike.ofReal_re, map_zero] at hz
    exact h.ne' hz
  · intro h
    apply lt_of_le_of_ne (rowSubsetVolume_nonneg X S)
    intro hz
    apply h
    rw [← hz, RCLike.ofReal_zero]

/-- A selected full-column minor survives padded row restriction exactly
when every one of its row labels belongs to the selected set. -/
theorem det_coordinateSelector_mul_submatrix (X : Matrix n d 𝕜)
    (S : Finset n) (J : SizedSubset n d) :
    (((coordinateSelector S : Matrix n n 𝕜) * X).submatrix (sizedSubsetIndex J) id).det =
      if J.val ⊆ S then (X.submatrix (sizedSubsetIndex J) id).det else 0 := by
  classical
  split_ifs with hJS
  · congr 1
    ext i j
    change ((coordinateSelector S : Matrix n n 𝕜) * X) (sizedSubsetIndex J i) j = X (sizedSubsetIndex J i) j
    rw [coordinateSelector_mul_apply]
    apply if_pos
    have hm : sizedSubsetIndex J i ∈ (J.val : Set n) :=
      range_sizedSubsetIndex J ▸ Set.mem_range_self i
    exact hJS hm
  · obtain ⟨a, haJ, haS⟩ := Finset.not_subset.mp hJS
    obtain ⟨i, hi⟩ := (range_sizedSubsetIndex J ▸ haJ : a ∈ Set.range (sizedSubsetIndex J))
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    change ((coordinateSelector S : Matrix n n 𝕜) * X) (sizedSubsetIndex J i) j = 0
    rw [coordinateSelector_mul_apply, hi, if_neg haS]

/-- Cauchy–Binet expands each row-volume weight over all full-column minors
contained in its row set. No rank or nonempty-dimension premise is used.
Dereziński–Warmuth 2018, proof of Theorem 2. -/
theorem rowSubsetVolume_eq_sum_minors (X : Matrix n d 𝕜) (S : Finset n) :
    rowSubsetVolume X S = ∑ J : SizedSubset n d,
      if J.val ⊆ S then ‖(X.submatrix (sizedSubsetIndex J) id).det‖ ^ 2 else 0 := by
  unfold rowSubsetVolume
  rw [rowSubsetGram_eq_conjTranspose_mul_self,
    det_conjTranspose_mul_self_eq_sum_norm_sq, RCLike.ofReal_re]
  apply Finset.sum_congr rfl
  intro J _
  rw [det_coordinateSelector_mul_submatrix]
  split_ifs <;> simp

/-- Adding rows cannot decrease their nonnegative Gram determinant. -/
theorem rowSubsetVolume_mono (X : Matrix n d 𝕜) {S T : Finset n} (hST : S ⊆ T) :
    rowSubsetVolume X S ≤ rowSubsetVolume X T := by
  rw [rowSubsetVolume_eq_sum_minors, rowSubsetVolume_eq_sum_minors]
  apply Finset.sum_le_sum
  intro J _
  by_cases hJS : J.val ⊆ S
  · rw [if_pos hJS, if_pos (hJS.trans hST)]
  · rw [if_neg hJS]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

/-- The same normalizer identity holds inside an arbitrary ambient row set.
This is the conditional law used after each reverse-deletion step. -/
theorem sum_rowSubsetVolume_powersetCard (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hds : Fintype.card d ≤ s) :
    (∑ S ∈ T.powersetCard s, rowSubsetVolume X S) =
      ((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T := by
  classical
  simp_rw [rowSubsetVolume_eq_sum_minors]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJT : J.val ⊆ T
  · rw [if_pos hJT, ← Finset.sum_filter, Finset.sum_const,
      Finset.card_filter_powersetCard_subset J.val T s hJT (by simpa only [J.property] using hds)]
    simp only [J.property, nsmul_eq_mul]
  · rw [if_neg hJT, mul_zero]
    apply Finset.sum_eq_zero
    intro S hS
    rw [if_neg (fun hJS => hJT (hJS.trans (Finset.mem_powersetCard.mp hS).1))]

/-- The total size-`s` row-volume weight is the binomial multiplicity times
the full Gram determinant. This identity also holds for deficient matrices.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem sum_rowSubsetVolume_eq_choose_mul (X : Matrix n d 𝕜) (s : ℕ)
    (hds : Fintype.card d ≤ s) :
    (∑ S ∈ (Finset.univ : Finset n).powersetCard s, rowSubsetVolume X S) =
      ((Fintype.card n - Fintype.card d).choose (s - Fintype.card d) : ℝ) *
        RCLike.re (Xᴴ * X).det := by
  classical
  simp_rw [rowSubsetVolume_eq_sum_minors]
  rw [Finset.sum_comm]
  have hGram := congrArg RCLike.re (det_conjTranspose_mul_self_eq_sum_norm_sq X)
  simp only [RCLike.ofReal_re] at hGram
  rw [hGram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_filter, Finset.sum_const,
    Finset.card_filter_powersetCard_subset J.val Finset.univ s (Finset.subset_univ _)
      (by simpa only [J.property] using hds)]
  simp only [Finset.card_univ, J.property, nsmul_eq_mul]

omit [DecidableEq n] in
/-- The full Gram determinant has positive real part when the columns are
independent. The hypothesis uses the native full-column Gram certificate. -/
theorem re_det_conjTranspose_mul_self_pos (X : Matrix n d 𝕜)
    (hX : IsUnit (Xᴴ * X)) : 0 < RCLike.re (Xᴴ * X).det := by
  have hnonneg := (RCLike.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self X).det_nonneg).1
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have him := (RCLike.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self X).det_nonneg).2
  apply ((Matrix.isUnit_iff_isUnit_det _).mp hX).ne_zero
  exact RCLike.ext (by simpa using hzero.symm) (by simpa using him)

/-- The row-volume normalizer is positive at every admissible sample size
for a full-column-rank matrix.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem sum_rowSubsetVolume_pos (X : Matrix n d 𝕜) (s : ℕ)
    (hX : IsUnit (Xᴴ * X)) (hds : Fintype.card d ≤ s) (hsn : s ≤ Fintype.card n) :
    0 < ∑ S ∈ (Finset.univ : Finset n).powersetCard s, rowSubsetVolume X S := by
  rw [sum_rowSubsetVolume_eq_choose_mul X s hds]
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hsn _)))
    (re_det_conjTranspose_mul_self_pos X hX)

end NLAlib
